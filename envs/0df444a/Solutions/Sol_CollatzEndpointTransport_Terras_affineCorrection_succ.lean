-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.affineCorrection_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:56.577371+00:00
-- url     : https://prove2.me/submissions/d4537eb2-8b96-4022-87c5-e65007e9ead6

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrectionTerm_succ_old
import Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrectionTerm_succ_last

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n : ℕ) :
    affineCorrection (k + 1) n =
      affineCorrection k n / 2 +
        parityDigitR n k /
          ((3 : ℝ) ^ oddCount (k + 1) n * 2) := by
  rw [affineCorrection, affineCorrection, Finset.sum_range_succ]
  calc
    (∑ x ∈ Finset.range k, affineCorrectionTerm (k + 1) n x) +
          affineCorrectionTerm (k + 1) n k =
        (∑ x ∈ Finset.range k, affineCorrectionTerm k n x / 2) +
          affineCorrectionTerm (k + 1) n k := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact affineCorrectionTerm_succ_old (Finset.mem_range.mp hi)
    _ = (∑ x ∈ Finset.range k, affineCorrectionTerm k n x) / 2 +
          parityDigitR n k /
            ((3 : ℝ) ^ oddCount (k + 1) n * 2) := by
      rw [Finset.sum_div, affineCorrectionTerm_succ_last]
end CollatzEndpointTransport.Terras
