-- Prove2me | solution 1 for ChromaticReconstruction.coeff_fP_lowerAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:36:56.913777+00:00
-- url     : https://prove2.me/submissions/1d525703-38b0-4d9f-ab76-e75d96189879

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_coeff_mono
import Theorems.Thm_ChromaticReconstruction_lowerAt_inj
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} {a : ℕ} (ha : a ∈ bigWeights W) :
    coeff (Multiset.toFinsupp (lowerAt W a)) (fP W) = (((a - 1) * W.count a : ℕ) : ℚ) := by
  unfold fP
  rw [coeff_sum, sum_eq_single a]
  · rw [coeff_C_mul, coeff_mono, if_pos rfl, mul_one]
  · intro b hb hba
    rw [coeff_C_mul, coeff_mono, if_neg, mul_zero]
    intro h
    simp only [bigWeights, mem_filter, Multiset.mem_toFinset] at ha hb
    exact hba (lowerAt_inj hb.1 ha.1 (by omega) (by omega) h)
  · intro h; exact absurd ha h
end ChromaticReconstruction
