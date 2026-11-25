-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.hilbertSchmidt_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:03:46.64393+00:00
-- url     : https://prove2.me/submissions/e3e251ff-e7f4-4fba-8f72-8249f50b9e35

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TorusArgumentMultiplicative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.HSFrame := by
  intro E E' _ _ _ _ _ _ U U' J₁ J₂
  have hadj : ∀ J : E' →L[ℂ] E, ContinuousLinearMap.adjoint (C7.frameConj U U' J) =
      (U'.symm.toContinuousLinearEquiv : E' →L[ℂ] E') ∘L ContinuousLinearMap.adjoint J ∘L
        (U.toContinuousLinearEquiv : E →L[ℂ] E) := by
    intro J
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [C7.frameConj, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [← U'.inner_map_map, LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left,
      ← U.inner_map_map (x := x), LinearIsometryEquiv.apply_symm_apply]
  have e : ((ContinuousLinearMap.adjoint (C7.frameConj U U' J₂) ∘L C7.frameConj U U' J₁ : E' →L[ℂ] E') :
      E' →ₗ[ℂ] E') = (U'.symm.toLinearEquiv).conj
        ((ContinuousLinearMap.adjoint J₂ ∘L J₁ : E' →L[ℂ] E') : E' →ₗ[ℂ] E') := by
    apply LinearMap.ext; intro x
    rw [hadj]
    simp [C7.frameConj, LinearEquiv.conj_apply]
  rw [e, LinearMap.trace_conj']
end Formalism.FourierDecayAlt.P
