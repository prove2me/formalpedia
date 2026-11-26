-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.pow_mul_card_residues_with_oddCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:45.567088+00:00
-- url     : https://prove2.me/submissions/e758df1c-6b60-4a03-98ed-cab928554a10

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_pow_mul_lowerBinomialSum_le
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K *
        ((Finset.univ.filter
          (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (1 + x) ^ H := by
  rw [card_residues_with_oddCount_le]
  exact pow_mul_lowerBinomialSum_le hx0 hx1 hKH
end CollatzEndpointTransport.Terras
