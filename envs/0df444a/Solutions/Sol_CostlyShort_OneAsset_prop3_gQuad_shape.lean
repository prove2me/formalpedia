-- Prove2me | solution 1 for CostlyShort.OneAsset.prop3_gQuad_shape
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:37:05.816315+00:00
-- url     : https://prove2.me/submissions/7930fef6-c4ce-4dfe-a3ee-982ebc5c7be6

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

set_option autoImplicit false
open CostlyShort.OneAsset Filter

namespace CSOH

/-- explicit quadratic form of `gQuad` -/
lemma gQuad_eq (σ Δ s γ : ℝ) :
    gQuad σ Δ s γ = -(s * (1 - s)) * γ ^ 2
      + (-(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2) * γ + (1 - s) * (s * Δ - σ) ^ 2 := by
  unfold gQuad; ring

lemma gQuad_fun (σ Δ s : ℝ) :
    gQuad σ Δ s = fun γ => -(s * (1 - s)) * γ ^ 2
      + (-(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2) * γ + (1 - s) * (s * Δ - σ) ^ 2 := by
  funext γ; exact gQuad_eq σ Δ s γ

lemma gQuad_hasDeriv (σ Δ s γ : ℝ) :
    HasDerivAt (gQuad σ Δ s)
      (-(2 * (s * (1 - s))) * γ + (-(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2)) γ := by
  rw [gQuad_fun]
  have h := ((((hasDerivAt_id γ).pow 2).const_mul (-(s * (1 - s)))).add
    ((hasDerivAt_id γ).const_mul (-(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2))).add_const
    ((1 - s) * (s * Δ - σ) ^ 2)
  refine h.congr_deriv ?_
  simp
  ring

end CSOH

theorem solution (σ s Δ : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1)
    (hreg : σ < s * Δ) :
    (gQuad σ Δ s 0 = (1 - s) * (s * Δ - σ) ^ 2 ∧ 0 < gQuad σ Δ s 0) ∧
    (deriv (gQuad σ Δ s) 0 = -σ * (1 + s) ^ 2 - (1 - s) ^ 2 * (s * Δ - σ) ∧
      deriv (gQuad σ Δ s) 0 < 0) ∧
    (∀ γ : ℝ, deriv (deriv (gQuad σ Δ s)) γ = -2 * s * (1 - s)) ∧
    Tendsto (gQuad σ Δ s) atTop atBot := by
  have h1s : 0 < 1 - s := by linarith
  have hu : 0 < s * Δ - σ := by linarith
  have hd : deriv (gQuad σ Δ s) = fun γ => -(2 * (s * (1 - s))) * γ
      + (-(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2) := by
    funext γ; exact (CSOH.gQuad_hasDeriv σ Δ s γ).deriv
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [CSOH.gQuad_eq]; ring
  · rw [CSOH.gQuad_eq]; simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, neg_zero, zero_add]
    positivity
  · rw [hd]; simp; ring
  · rw [hd]; simp
    have : 0 < (1 - s) ^ 2 * (s * Δ - σ) := by positivity
    have : 0 < σ * (1 + s) ^ 2 := by positivity
    nlinarith
  · intro γ
    rw [hd]
    have h : HasDerivAt (fun γ : ℝ => -(2 * (s * (1 - s))) * γ
        + (-(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2)) (-(2 * (s * (1 - s)))) γ := by
      simpa using ((hasDerivAt_id γ).const_mul (-(2 * (s * (1 - s))))).add_const
        (-(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2)
    rw [h.deriv]; ring
  · rw [CSOH.gQuad_fun]
    have ha : 0 < s * (1 - s) := by positivity
    -- γ * (-(a γ) + B) + C
    have h1 : Tendsto (fun γ : ℝ => -(s * (1 - s)) * γ
        + (-(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2)) atTop atBot := by
      have := (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).const_mul_atTop_of_neg (r := -(s * (1 - s))) (by linarith)
      exact tendsto_atBot_add_const_right _ _ this
    have h2 := (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).atTop_mul_atBot₀ h1
    have h3 := tendsto_atBot_add_const_right _ ((1 - s) * (s * Δ - σ) ^ 2) h2
    refine h3.congr ?_
    intro γ
    simp
    ring
