-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.length_le_of_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:57.392117+00:00
-- url     : https://prove2.me/submissions/92a07b52-806a-4919-937c-b703267a4b30

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_lengthBaseChangeLocal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
  [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution {Q Q' : Type} [AddCommGroup Q] [Module O Q] [AddCommGroup Q']
    [Module O' Q'] (ϖ : O) (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ))
    (g : Q →ₛₗ[algebraMap O O'] Q') (hg : Submodule.span O' (Set.range g) = ⊤) :
    Module.length O' Q' ≤ Module.length O Q := by
  by_cases hQ : Module.length O Q = ⊤
  · rw [hQ]; exact le_top
  let _ : Module O Q' := Module.compHom Q' (algebraMap O O')
  have : IsScalarTower O O' Q' := ⟨fun a b x => by
    show (a • b) • x = (algebraMap O O' a) • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let g' : Q →ₗ[O] Q' :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun a x => g.map_smulₛₗ a x }
  have hs : Function.Surjective (g'.liftBaseChange O') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨TensorProduct.tmul O 1 x, by rw [LinearMap.liftBaseChange_tmul, one_smul]; rfl⟩
  have h := Module.length_le_of_surjective _ hs
  rw [lengthBaseChangeLocal O O' Q ϖ (algebraMap O O' ϖ) 1 1 hϖ hϖ' (by simp) hQ] at h
  simpa using h
end Formalism.MainNotions.Gaps.T0
