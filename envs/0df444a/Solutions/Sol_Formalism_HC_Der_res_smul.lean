-- Prove2me | solution 1 for Formalism.HC.Der.res_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:32.642748+00:00
-- url     : https://prove2.me/submissions/041e50ab-0dc7-4148-98a4-f8d9902ecd6b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsScalarTower ℚ E L]
omit [IsScalarTower ℚ E L]
namespace Formalism.HC.Der
theorem _root_.solution (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L) (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (x : 𝓞 E) :
    algebraMap (𝓞 E) (𝓞 L) (σ • x) = τ • algebraMap (𝓞 E) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  exact h x
end Formalism.HC.Der
