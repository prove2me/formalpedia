-- Prove2me | solution 1 for Formalism.L2.Th1.H.precompHeisenberg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:30.735805+00:00
-- url     : https://prove2.me/submissions/41525fe7-7bbb-4d7b-a6cd-3568bdd29d30

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : PullOpU := by
  intro V _ _ H δ hδ x F z
  have h1 : H z (δ x) = H (δ.symm z) x := by
    have h := hδ (δ.symm z) x
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
    exact h
  have h2 : H (δ x) (δ x) = H x x := by
    have h := hδ x x
    simpa only [LinearEquiv.coe_coe] using h
  simp only [pullInv, opU, map_add, LinearEquiv.symm_apply_apply, h1, h2]
end Formalism.L2.Th1.H
