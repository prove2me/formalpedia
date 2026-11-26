-- Prove2me | solution 1 for ChandrasekaranNullCone.clock_distance_5_7
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-26T15:35:05.216999+00:00
-- url     : https://prove2.me/submissions/f8165ccc-e7ad-47ee-bc6b-6dddfd17c16f

import Mathlib

open MeasureTheory

namespace ChandrasekaranNullCone.Clock57

/-- A bounded measurable real multiplier of `‖ω‖²` keeps it integrable. -/
lemma integrable_mul_normSq {X : Type*} [MeasurableSpace X] {μ : Measure X} {ω : X → ℂ}
    (hω : MemLp ω 2 μ) {g : X → ℝ} (hg : Measurable g) {c : ℝ} (hgc : ∀ x, ‖g x‖ ≤ c) :
    Integrable (fun x => g x * ‖ω x‖ ^ 2) μ :=
  (hω.integrable_norm_pow two_ne_zero).bdd_mul (c := c) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hgc)

end ChandrasekaranNullCone.Clock57

open ChandrasekaranNullCone.Clock57 in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (L : ℝ) (hL : 0 < L) (ω : X → ℂ)
    (hω : MemLp ω 2 μ) (hnorm : ∫ x, ‖ω x‖ ^ 2 ∂μ = 1) :
    let ψL : X → ℂ := fun x => ((L / (L + u x) : ℝ) : ℂ) * ω x
    (∫ x, ‖ω x - ψL x‖ ^ 2 ∂μ) ≤ 1 - (∫ x, star (ω x) * ψL x ∂μ).re ∧
      1 - (∫ x, star (ω x) * ψL x ∂μ).re = ∫ x, u x / (L + u x) * ‖ω x‖ ^ 2 ∂μ := by
  intro ψL
  have hpos : ∀ x, 0 < L + u x := fun x => by linarith [hu0 x]
  have hb1 : ∀ x, ‖L / (L + u x)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL, abs_of_pos (hpos x), div_le_one (hpos x)]
    linarith [hu0 x]
  have hb2 : ∀ x, ‖u x / (L + u x)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hu0 x), abs_of_pos (hpos x),
      div_le_one (hpos x)]; linarith
  have hb3 : ∀ x, ‖(u x / (L + u x)) ^ 2‖ ≤ 1 := fun x => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hb2 x)
  have hI1 := integrable_mul_normSq hω (g := fun x => L / (L + u x)) (by fun_prop) hb1
  have hI2 := integrable_mul_normSq hω (g := fun x => u x / (L + u x)) (by fun_prop) hb2
  have hI3 := integrable_mul_normSq hω (g := fun x => (u x / (L + u x)) ^ 2) (by fun_prop) hb3
  have hI0 : Integrable (fun x => ‖ω x‖ ^ 2) μ := hω.integrable_norm_pow two_ne_zero
  have hinner : ∫ x, star (ω x) * ψL x ∂μ = ((∫ x, L / (L + u x) * ‖ω x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ψL]
    rw [mul_left_comm, Complex.star_def, Complex.conj_mul']
    push_cast; ring
  have hre : 1 - (∫ x, star (ω x) * ψL x ∂μ).re = ∫ x, u x / (L + u x) * ‖ω x‖ ^ 2 ∂μ := by
    rw [hinner, Complex.ofReal_re, ← hnorm, ← integral_sub hI0 hI1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have := (hpos x).ne'
    field_simp; ring
  refine ⟨?_, hre⟩
  rw [hre]
  have hdist : ∫ x, ‖ω x - ψL x‖ ^ 2 ∂μ = ∫ x, (u x / (L + u x)) ^ 2 * ‖ω x‖ ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hne : L + u x ≠ 0 := (hpos x).ne'
    have hne' : (L : ℂ) + u x ≠ 0 := by exact_mod_cast hne
    have : ω x - ψL x = (((u x / (L + u x)) : ℝ) : ℂ) * ω x := by
      simp only [ψL]; push_cast; field_simp; ring
    dsimp only
    rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hdist]
  refine integral_mono hI3 hI2 fun x => ?_
  have h0 : 0 ≤ u x / (L + u x) := div_nonneg (hu0 x) (hpos x).le
  have h1 : u x / (L + u x) ≤ 1 := by rw [div_le_one (hpos x)]; linarith
  have : (u x / (L + u x)) ^ 2 ≤ u x / (L + u x) := by nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)
