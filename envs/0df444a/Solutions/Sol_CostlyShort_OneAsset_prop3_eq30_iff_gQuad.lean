-- Prove2me | solution 1 for CostlyShort.OneAsset.prop3_eq30_iff_gQuad
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:34:57.059106+00:00
-- url     : https://prove2.me/submissions/cdfddd00-18c3-42a4-8023-bce306405369

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

theorem solution (σ s Δ γ : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) :
    (σ * γ = (1 - s) * (s * (σ * Δ) - σ * γ - σ ^ 2) * ((σ * Δ + σ * γ) * s - σ ^ 2)
        / (σ ^ 2 * (1 + s) ^ 2)) ↔ gQuad σ Δ s γ = 0 := by
  have hden : σ ^ 2 * (1 + s) ^ 2 ≠ 0 := by positivity
  rw [eq_div_iff hden]
  have key : (1 - s) * (s * (σ * Δ) - σ * γ - σ ^ 2) * ((σ * Δ + σ * γ) * s - σ ^ 2)
      - σ * γ * (σ ^ 2 * (1 + s) ^ 2) = σ ^ 2 * gQuad σ Δ s γ := by
    unfold gQuad; ring
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    have h0 : σ ^ 2 * gQuad σ Δ s γ = 0 := by rw [← key]; linarith
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hσ2
    · exact h1
  · intro h
    rw [h, mul_zero] at key
    linarith
