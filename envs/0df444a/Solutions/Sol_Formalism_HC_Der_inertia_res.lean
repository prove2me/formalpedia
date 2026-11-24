-- Prove2me | solution 1 for Formalism.HC.Der.inertia_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:19.677842+00:00
-- url     : https://prove2.me/submissions/d36af126-ecd9-4653-af38-996f1338494a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Theorems.Thm_Formalism_HC_Der_res_smul
import Theorems.Thm_Formalism_HC_Der_mem_over_iff

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
theorem _root_.solution (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P] (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L)
    (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (hτ : ∀ y : 𝓞 L, τ • y - y ∈ Q) (x : 𝓞 E) :
    σ • x - x ∈ P := by
  rw [mem_over_iff P Q, map_sub, res_smul σ τ h]
  exact hτ _
end Formalism.HC.Der
