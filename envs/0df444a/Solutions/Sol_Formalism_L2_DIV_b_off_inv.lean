-- Prove2me | solution 1 for Formalism.L2.DIV.b_off_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:06.647105+00:00
-- url     : https://prove2.me/submissions/1ed86e96-109b-4b01-b9d4-34385fc81e61

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_toRInt_alg
import Theorems.Thm_Formalism_L2_DIV_b_eps_val
import Theorems.Thm_Formalism_L2_DIV_b_inv_int
import Theorems.Thm_Formalism_L2_DIV_b_alg_ne_zero
import Theorems.Thm_Formalism_UG_P_afsplitI_ne
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_afsplit_one_apply
import Theorems.Thm_Formalism_UG_P_afsplit_sub_apply
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F)
    (hr : ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → r ∉ v'.asIdeal) :
    ∃ ρ : RInt F E, toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ρ = 1 - bEps E v := by
  classical
  have hint : ∀ w : HeightOneSpectrum (𝓞 F),
      (if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹) ∈
        w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · exact zero_mem _
    · exact b_inv_int w r (hr w h)
  let a : FiniteAdeleRing (𝓞 F) F :=
    ⟨fun w => if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹,
      Filter.Eventually.of_forall hint⟩
  have ha : a ∈ intAd F := hint
  refine ⟨⟨(1 : E) ⊗ₜ[F] a, ?_⟩, ?_⟩
  · have := levelaf_tmul_mem (F := F) (E := E) 1 ha
    rwa [map_one] at this
  · apply Subtype.ext
    show ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) : RInt F E) : AfE F E) * _ = 1 - afsplitEps E v
    rw [b_toRInt_alg, Algebra.TensorProduct.tmul_mul_tmul, one_mul, b_eps_val, Algebra.TensorProduct.one_def,
      ← TensorProduct.tmul_sub]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    rw [afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply]
    show algebraMap (𝓞 F) (w.adicCompletion F) r *
      (if w = v then (0 : w.adicCompletion F) else (algebraMap (𝓞 F) (w.adicCompletion F) r)⁻¹) = _
    by_cases h : w = v
    · subst h
      rw [if_pos rfl, afsplitI_self, mul_zero, sub_self]
    · rw [if_neg h, afsplitI_ne v w h, sub_zero]
      exact mul_inv_cancel₀ (b_alg_ne_zero w r (hr w h))
end Formalism.L2.DIV
