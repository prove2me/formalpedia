-- Prove2me | solution 1 for Formalism.L2.LamCM.absNorm_bcI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:55.626259+00:00
-- url     : https://prove2.me/submissions/aae1736b-f532-4f2d-9d99-b5aad47e6ed1

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
import Theorems.Thm_Formalism_L2_LamCM_bcI_mul
import Theorems.Thm_Formalism_L2_LamCM_bcI_spanSingleton
import Theorems.Thm_Formalism_L2_LamCM_bcI_coeIdeal
import Theorems.Thm_P2M_Formalism_L2_LamCM_absNorm_coeIdeal__23f234ea3c14
import Theorems.Thm_Formalism_L2_LamCM_finrank_int_eq
import Theorems.Thm_Formalism_L2_LamCM_norm_algebraMap_tower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
namespace Formalism.L2.LamCM
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.absNorm (bcI (K1 := K1) I) = (FractionalIdeal.absNorm I) ^ Module.finrank K K1 := by
  have hJ : ∀ J : Ideal (𝓞 K), FractionalIdeal.absNorm (bcI (K1 := K1) (J : FractionalIdeal (𝓞 K)⁰ K)) =
      FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) ^ Module.finrank K K1 := by
    intro J
    rw [bcI_coeIdeal, absNorm_coeIdeal', absNorm_coeIdeal']
    have h3 := Ideal.absNorm_relNorm (𝓞 K) (𝓞 K1) (J.map (algebraMap (𝓞 K) (𝓞 K1)))
    rw [Ideal.relNorm_algebraMap, map_pow, finrank_int_eq] at h3
    rw [← h3, Nat.cast_pow]
  have hx : ∀ x : K, FractionalIdeal.absNorm (bcI (K1 := K1) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) =
      FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) ^ Module.finrank K K1 := by
    intro x
    rw [bcI_spanSingleton, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.absNorm_span_singleton,
      norm_algebraMap_tower, abs_pow]
  have e := FractionalIdeal.den_mul_self_eq_num' (𝓞 K)⁰ K I
  have e1 := congrArg (fun J => FractionalIdeal.absNorm (bcI (K1 := K1) J)) e
  have e0 := congrArg FractionalIdeal.absNorm e
  simp only [bcI_mul, map_mul] at e1 e0
  rw [hx, hJ, ← e0, mul_pow] at e1
  have hne : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰
      (algebraMap (𝓞 K) K (I.den : 𝓞 K))) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  exact mul_left_cancel₀ (pow_ne_zero _ hne) e1
end Formalism.L2.LamCM
