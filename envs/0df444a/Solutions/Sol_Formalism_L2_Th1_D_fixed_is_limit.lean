-- Prove2me | solution 1 for Formalism.L2.Th1.D.fixed_is_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:02:39.656308+00:00
-- url     : https://prove2.me/submissions/3e16fd9f-8492-4c05-b0cb-1926a56ede59

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_poly_id
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_norm_eval_le
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_norm_le_inv_of_lt_one
import Theorems.Thm_Formalism_LT_TorsProof_norm_eval_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open TraceNormBounds
namespace Formalism.L2.Th1.D
theorem _root_.solution : FixedIsLimit := by
  intro K _ _ _ l σ hU
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hinv : ((l : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have step : ∀ x : K, ‖x‖ ≤ 1 → σ x = x → ∃ n : ℕ, ‖x - n‖ ≤ (l : ℝ)⁻¹ := by
    intro x hx hfix
    obtain ⟨Q, hQ⟩ := poly_id l hp
    have hev := congrArg (Polynomial.eval₂ (Int.castRingHom K) x) hQ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_finsetProd] at hev
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_natCast, eq_intCast,
      Int.cast_natCast] at hev
    have h1 : ‖x ^ l - x‖ ≤ (l : ℝ)⁻¹ := by
      have := hσ x hx
      rwa [hfix, norm_sub_rev] at this
    have h2 : ‖(l : K) * Polynomial.eval₂ (Int.castRingHom K) x Q‖ ≤ (l : ℝ)⁻¹ := by
      rw [norm_mul, hpn]
      exact mul_le_of_le_one_right (by positivity) (norm_eval_le Q hx)
    have h3 : ‖∏ n ∈ Finset.range l, (x - (n : K))‖ ≤ (l : ℝ)⁻¹ := by
      have e : ∏ n ∈ Finset.range l, (x - (n : K)) =
          (x ^ l - x) - (l : K) * Polynomial.eval₂ (Int.castRingHom K) x Q := by
        rw [← hev]; ring
      rw [e, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
    by_contra hc
    push Not at hc
    have h4 : ∀ n ∈ Finset.range l, (1 : ℝ) ≤ ‖x - (n : K)‖ := by
      intro n _
      by_contra hlt
      exact absurd (norm_le_inv_of_lt_one hp.one_lt hval (not_le.1 hlt)) (not_le.2 (hc n))
    have h5 : (1 : ℝ) ≤ ‖∏ n ∈ Finset.range l, (x - (n : K))‖ := by
      rw [norm_prod]
      have := Finset.prod_le_prod (s := Finset.range l) (f := fun _ => (1 : ℝ))
        (g := fun n : ℕ => ‖x - (n : K)‖) (fun _ _ => zero_le_one) h4
      simpa using this
    linarith
  intro x hx hfix k
  induction k generalizing x with
  | zero => exact ⟨0, by simpa using hx⟩
  | succ k ih =>
    obtain ⟨n0, hn0⟩ := step x hx hfix
    have hy : ‖(x - n0) / (l : K)‖ ≤ 1 := by
      rw [norm_div, hpn, div_inv_eq_mul]
      calc ‖x - n0‖ * l ≤ (l : ℝ)⁻¹ * l := by gcongr
        _ = 1 := inv_mul_cancel₀ hl0
    have hyf : σ ((x - n0) / (l : K)) = (x - n0) / (l : K) := by
      rw [map_div₀, map_sub, map_natCast, map_natCast, hfix]
    obtain ⟨m, hm⟩ := ih _ hy hyf
    refine ⟨n0 + l * m, ?_⟩
    have e : x - ((n0 + l * m : ℕ) : K) = (l : K) * ((x - n0) / (l : K) - m) := by
      push_cast
      field_simp
      ring
    rw [e, norm_mul, hpn, pow_succ, mul_inv, mul_comm]
    gcongr
end Formalism.L2.Th1.D
