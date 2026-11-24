-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.liftM_int_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:22.387935+00:00
-- url     : https://prove2.me/submissions/98dbfa41-c89d-4c43-b9c9-eaecbc628d38

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LiftMOneExt
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_val_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (e : 𝓞 E) :
    liftM M (σ (algebraMap (𝓞 E) E e)) ∈ (algebraMap (𝓞 M) M).range := by
  have h1 : IsIntegral ℤ (σ (algebraMap (𝓞 E) E e)) :=
    (RingOfIntegers.isIntegral_coe e).map σ.toIntAlgHom
  have hx : IsIntegral ℤ (liftM M (σ (algebraMap (𝓞 E) E e))) := by
    rw [← isIntegral_algHom_iff (algebraMap M ℂ).toIntAlgHom (algebraMap M ℂ).injective]
    change IsIntegral ℤ ((liftM M (σ (algebraMap (𝓞 E) E e)) : M) : ℂ)
    rwa [liftM_val_ext (hσ _)]
  exact ⟨⟨_, hx⟩, rfl⟩
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
