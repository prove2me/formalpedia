-- Prove2me | solution 1 for CostlyShort.OneAsset.eq33_eq34_yield_from_cost
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:34:57.986989+00:00
-- url     : https://prove2.me/submissions/47e8fd29-28de-459a-89c7-cf78d34bc35b

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
    (hδ : 0 ≤ δ) :
    yieldOne σ δ s = costOne σ δ s * ((1 - s) / σ ^ 2 * costOne σ δ s)
      / (1 + (1 - s) / σ ^ 2 * costOne σ δ s) := by
  by_cases hg : σ ^ 2 < s * δ
  · unfold yieldOne costOne
    simp only [if_pos hg]
    set r := Real.sqrt (s ^ 2 * (1 - s) ^ 2 * δ ^ 2 + 4 * σ ^ 4 * s) with hr
    have hr2 : r ^ 2 = s ^ 2 * (1 - s) ^ 2 * δ ^ 2 + 4 * σ ^ 4 * s := Real.sq_sqrt (by positivity)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have h1s : 0 < 1 - s := by linarith
    have hδp : 0 < δ := by
      by_contra h
      have : δ ≤ 0 := not_lt.mp h
      nlinarith [sq_nonneg σ]
    have hne : 1 + (1 - s) / σ ^ 2 * ((s * (1 - s) * δ - 2 * σ ^ 2 + r) / (2 * (1 - s))) ≠ 0 := by
      have : 1 + (1 - s) / σ ^ 2 * ((s * (1 - s) * δ - 2 * σ ^ 2 + r) / (2 * (1 - s)))
          = (s * (1 - s) * δ + r) / (2 * σ ^ 2) := by
        field_simp; ring
      rw [this]
      have : 0 < s * (1 - s) * δ + r := by positivity
      positivity
    rw [eq_div_iff hne]
    field_simp
    linear_combination hr2
  · unfold yieldOne costOne
    simp only [if_neg hg]
    simp
