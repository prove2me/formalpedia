-- Prove2me | solution 1 for ChromaticReconstruction.coeff_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:42:29.421144+00:00
-- url     : https://prove2.me/submissions/be081538-7934-4cfb-b9c8-555624b5036d

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (μ ν : Multiset ℕ) :
    coeff (Multiset.toFinsupp ν) (mono μ) = if μ = ν then 1 else 0 := by
  unfold mono
  rw [coeff_monomial]
  simp only [EmbeddingLike.apply_eq_iff_eq]
end ChromaticReconstruction
