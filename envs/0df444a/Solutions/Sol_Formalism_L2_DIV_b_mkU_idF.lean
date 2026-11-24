-- Prove2me | solution 1 for Formalism.L2.DIV.b_mkU_idF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:02.096362+00:00
-- url     : https://prove2.me/submissions/2b925e33-1b5b-45cc-a7d5-e2a005ad6806

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_toRInt_alg
import Theorems.Thm_Formalism_L2_DIV_b_eps_val
import Theorems.Thm_Formalism_L2_DIV_b_alg_ne_zero
import Theorems.Thm_Formalism_UG_P_afsplitI_ne
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_afsplit_one_apply
import Theorems.Thm_Formalism_UG_P_afsplit_sub_apply


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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (n : 𝓞 F) (hn : n ∉ v.asIdeal) (u : (RInt F E)ˣ)
    (hu : (u : RInt F E) = toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) * bEps E v + (1 - bEps E v)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ (idF F E).range := by
  set nv := algebraMap (𝓞 F) (v.adicCompletion F) n with hnv
  have hn0 : nv ≠ 0 := b_alg_ne_zero v n hn
  have hmul : (afsplitI v nv + (1 - afsplitI v 1)) * (afsplitI v nv⁻¹ + (1 - afsplitI v 1)) = 1 := by
    refine FiniteAdeleRing.ext _ fun w => ?_
    by_cases h : w = v
    · subst h
      simp only [afsplit_mul_apply, afsplit_add_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_self, sub_self,
        add_zero]
      exact mul_inv_cancel₀ hn0
    · simp only [afsplit_mul_apply, afsplit_add_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_ne v w h,
        sub_zero, zero_add, mul_one]
  refine ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, ?_⟩
  apply Units.ext
  show (1 : E) ⊗ₜ[F] (afsplitI v nv + (1 - afsplitI v 1)) = ((u : RInt F E) : AfE F E)
  rw [hu]
  show _ = ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) : RInt F E) : AfE F E) * afsplitEps E v + (1 - afsplitEps E v)
  rw [b_toRInt_alg, b_eps_val, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.one_def,
    ← TensorProduct.tmul_sub, ← TensorProduct.tmul_add]
  congr 2
  refine FiniteAdeleRing.ext _ fun w => ?_
  by_cases h : w = v
  · subst h
    rw [afsplit_mul_apply, afsplitI_self, afsplitI_self, mul_one]
    rfl
  · rw [afsplit_mul_apply, afsplitI_ne v w h, afsplitI_ne v w h, mul_zero]
end Formalism.L2.DIV
