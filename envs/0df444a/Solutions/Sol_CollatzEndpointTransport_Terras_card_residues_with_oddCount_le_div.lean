-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:47.779509+00:00
-- url     : https://prove2.me/submissions/5137c403-4bac-4767-8fa6-e4e83bf1f5d5

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_lowerBinomialSum_le_div
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (1 + x) ^ H / x ^ K := by
  rw [card_residues_with_oddCount_le]
  exact lowerBinomialSum_le_div hx0 hx1 hKH
end CollatzEndpointTransport.Terras
