-- Prove2me | solution 1 for Eden.singularValueFunction_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:28.027821+00:00
-- url     : https://prove2.me/submissions/2e66c663-af1c-4eb4-8b05-c0129cf739c6

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
import Theorems.Thm_Eden_spectralProduct_top

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    singularValueFunction A 5 = |A.det| := by
  change spectralProduct 5 (fun i => A.singularValues i) (5 : ℕ) = _
  rw [spectralProduct_top]
  have h := A.normDet_eq_prod_singularValues
  rw [finrank_euclideanSpace_fin] at h
  exact h.symm.trans A.normDet_eq_abs_det
end Eden
