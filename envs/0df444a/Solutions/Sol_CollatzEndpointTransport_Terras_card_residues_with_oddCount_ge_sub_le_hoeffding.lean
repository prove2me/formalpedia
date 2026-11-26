-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub_le_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:09.507118+00:00
-- url     : https://prove2.me/submissions/607a90fc-baa5-4f71-b363-373da77d7426

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_lowerBinomialSum_le_hoeffding
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_ge_sub

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by
  have hKHreal : (K : ℝ) ≤ H := by
    calc
      (K : ℝ) ≤ (1 / 2 - t) * H := hcut
      _ ≤ H := by
        have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
        nlinarith
  have hKH : K ≤ H := by exact_mod_cast hKHreal
  rw [card_residues_with_oddCount_ge_sub H K hKH]
  exact lowerBinomialSum_le_hoeffding ht hcut
end CollatzEndpointTransport.Terras
