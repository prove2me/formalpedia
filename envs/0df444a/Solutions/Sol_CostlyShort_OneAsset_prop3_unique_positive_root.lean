-- Prove2me | solution 1 for CostlyShort.OneAsset.prop3_unique_positive_root
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:37:06.897017+00:00
-- url     : https://prove2.me/submissions/ce073389-4f16-428b-8fb1-2034e0ff050c

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
    ∃! γ : ℝ, 0 < γ ∧ gQuad σ Δ s γ = 0 := by
  have h1s : 0 < 1 - s := by linarith
  have hu : 0 < s * Δ - σ := by linarith
  set a : ℝ := s * (1 - s) with ha
  set B : ℝ := -(1 - s) ^ 2 * (s * Δ - σ) - σ * (1 + s) ^ 2 with hB
  set C : ℝ := (1 - s) * (s * Δ - σ) ^ 2 with hC
  have hapos : 0 < a := by positivity
  have hCpos : 0 < C := by positivity
  have hg : ∀ γ, gQuad σ Δ s γ = -a * γ ^ 2 + B * γ + C := fun γ => CSOH.gQuad_eq σ Δ s γ
  set q : ℝ := Real.sqrt (B ^ 2 + 4 * a * C) with hq
  have hq2 : q ^ 2 = B ^ 2 + 4 * a * C := Real.sq_sqrt (by positivity)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqB : B < q := by
    by_contra h
    have h' : q ≤ B := not_lt.mp h
    have : q ^ 2 ≤ B ^ 2 := by nlinarith
    nlinarith [mul_pos hapos hCpos]
  refine ⟨(B + q) / (2 * a), ⟨?_, ?_⟩, ?_⟩
  · apply div_pos
    · by_contra h
      have h' : B + q ≤ 0 := not_lt.mp h
      have : q ≤ -B := by linarith
      have : q ^ 2 ≤ B ^ 2 := by nlinarith
      nlinarith [mul_pos hapos hCpos]
    · positivity
  · rw [hg]
    field_simp
    nlinarith [hq2]
  · rintro y ⟨hy, hgy⟩
    rw [hg] at hgy
    set z : ℝ := (B + q) / (2 * a) with hz
    have hzpos : 0 < z := by
      apply div_pos
      · by_contra h
        have h' : B + q ≤ 0 := not_lt.mp h
        have : q ≤ -B := by linarith
        have : q ^ 2 ≤ B ^ 2 := by nlinarith
        nlinarith [mul_pos hapos hCpos]
      · positivity
    have hzroot : -a * z ^ 2 + B * z + C = 0 := by
      rw [hz]; field_simp; nlinarith [hq2]
    have hfac : (y - z) * (a * (y + z) - B) = 0 := by nlinarith
    rcases mul_eq_zero.1 hfac with h | h
    · linarith
    · exfalso
      have hB' : B = a * (y + z) := by linarith
      have : a * y * z + C = 0 := by
        have : -a * y ^ 2 + a * (y + z) * y + C = 0 := by rw [← hB']; exact hgy
        nlinarith
      have : 0 < a * y * z := by positivity
      linarith
