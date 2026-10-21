-- Prove2me | solution 1 for CostlyShort.OneAsset.prop3_eq32_solves_eq30
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:34:58.956217+00:00
-- url     : https://prove2.me/submissions/39e25969-5175-45f5-bd3c-1202d2a4acee

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

theorem solution (σ δ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1)
    (hreg : σ ^ 2 < s * δ) :
    0 < yieldOne σ δ s ∧
    yieldOne σ δ s = (1 - s) * (s * δ - yieldOne σ δ s - σ ^ 2) * ((δ + yieldOne σ δ s) * s - σ ^ 2)
      / (σ ^ 2 * (1 + s) ^ 2) := by
  unfold yieldOne
  simp only [if_pos hreg]
  set r := Real.sqrt (s ^ 2 * (1 - s) ^ 2 * δ ^ 2 + 4 * σ ^ 4 * s) with hr
  have hr2 : r ^ 2 = s ^ 2 * (1 - s) ^ 2 * δ ^ 2 + 4 * σ ^ 4 * s := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have h1s : 0 < 1 - s := by linarith
  have hδp : 0 < δ := by
    by_contra h
    have : δ ≤ 0 := not_lt.mp h
    nlinarith [sq_nonneg σ]
  constructor
  · have hlt : s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2) < (1 + s) * r := by
      by_contra h
      have h' : (1 + s) * r ≤ s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2) := not_lt.mp h
      have hb : 0 ≤ (1 + s) * r := by positivity
      have hsq : ((1 + s) * r) ^ 2 ≤ (s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hb h' 2
      have hx : 0 < s * (1 - s) ^ 2 * (s * δ - σ ^ 2) ^ 2 := by
        have : 0 < s * δ - σ ^ 2 := by linarith
        positivity
      have : ((1 + s) * r) ^ 2 - (s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) ^ 2
          = 4 * (s * (1 - s) ^ 2 * (s * δ - σ ^ 2) ^ 2) := by
        rw [mul_pow, hr2]; ring
      linarith
    apply div_pos
    · linarith
    · positivity
  · rw [eq_div_iff (by positivity)]
    field_simp
    linear_combination (1 + s) ^ 2 * hr2
