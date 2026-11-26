-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.pow_mul_card_residues_with_oddCount_ge_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:27.935153+00:00
-- url     : https://prove2.me/submissions/1f0289b0-c26f-4cf7-99bd-d53b625fe0a9

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_pow_mul_lowerBinomialSum_le
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_ge_sub

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K *
        ((Finset.univ.filter
          (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) ≤
      (1 + x) ^ H := by
  rw [card_residues_with_oddCount_ge_sub H K hKH]
  exact pow_mul_lowerBinomialSum_le hx0 hx1 hKH
end CollatzEndpointTransport.Terras
