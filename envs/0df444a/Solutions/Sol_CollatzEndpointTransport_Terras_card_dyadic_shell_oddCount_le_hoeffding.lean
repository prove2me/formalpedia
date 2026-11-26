-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_le_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:36.240672+00:00
-- url     : https://prove2.me/submissions/bf1a44b2-8499-4a7a-bbe4-8dc7f7170a90

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_oddCount_le
import Theorems.Thm_CollatzEndpointTransport_Terras_lowerBinomialSum_le_hoeffding


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H M K : ℕ} {t : ℝ} (hHM : H ≤ M) (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => oddCount H n ≤ K)).card : ℝ) ≤
      (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
  rw [card_dyadic_shell_oddCount_le hHM, Nat.cast_mul, Nat.cast_pow]
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
