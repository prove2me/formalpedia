-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_ge_sub_le_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:36.875847+00:00
-- url     : https://prove2.me/submissions/4e0ff3e8-cb60-4336-b04b-ae214dde5f52

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_oddCount_ge_sub
import Theorems.Thm_CollatzEndpointTransport_Terras_lowerBinomialSum_le_hoeffding


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H M K : ℕ} {t : ℝ} (hHM : H ≤ M) (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => H - K ≤ oddCount H n)).card : ℝ) ≤
      (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
  have hKHreal : (K : ℝ) ≤ H := by
    calc
      (K : ℝ) ≤ (1 / 2 - t) * H := hcut
      _ ≤ H := by
        have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
        nlinarith
  have hKH : K ≤ H := by exact_mod_cast hKHreal
  rw [card_dyadic_shell_oddCount_ge_sub hHM hKH, Nat.cast_mul, Nat.cast_pow]
  have htail := lowerBinomialSum_le_hoeffding ht hcut
  calc
    (2 : ℝ) ^ (M - H) * (lowerBinomialSum H K : ℝ) ≤
        (2 : ℝ) ^ (M - H) *
          ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
end CollatzEndpointTransport.Terras
