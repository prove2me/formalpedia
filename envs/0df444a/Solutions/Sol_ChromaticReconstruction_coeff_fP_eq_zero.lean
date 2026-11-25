-- Prove2me | solution 1 for ChromaticReconstruction.coeff_fP_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:31:14.11863+00:00
-- url     : https://prove2.me/submissions/9d7c8d6b-92ef-410c-b0b8-213086bd22fc

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_coeff_mono

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} {ν : Multiset ℕ}
    (h : ∀ a ∈ bigWeights W, lowerAt W a ≠ ν) :
    coeff (Multiset.toFinsupp ν) (fP W) = 0 := by
  unfold fP
  rw [coeff_sum]
  apply sum_eq_zero
  intro a ha
  rw [coeff_C_mul, coeff_mono, if_neg (h a ha), mul_zero]
end ChromaticReconstruction
