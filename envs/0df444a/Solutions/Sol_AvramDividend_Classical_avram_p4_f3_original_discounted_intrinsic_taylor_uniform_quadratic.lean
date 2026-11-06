-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_uniform_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:49:00.335362+00:00
-- url     : https://prove2.me/submissions/58c83afa-2b0b-49e7-917d-f79be9ae4e46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original discounted predividend Taylor remainder, uniformly quadratic in small negative jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 a))
    (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min l 1 ∧ 0 ≤ C ∧
      (let U : ℝ≥0 × Ω → ℝ := fun p =>
        let y := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
        if y ∈ Icc l u then y else l
      let A : ℝ≥0 × Ω → ℝ := fun p =>
        if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
      ∀ p : ℝ≥0 × Ω, ∀ z ∈ Ioo (-r) (0 : ℝ),
        |A p * SpectrallyNegativeLevy.generatorIntegrand f (U p) z| ≤
          C * z ^ 2) := by
  classical
  obtain ⟨r, C, hr, hrle, hC, hbound⟩ :=
    avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
      X f a l u hl hlu hu hf
  refine ⟨r, C, hr, hrle, hC, ?_⟩
  dsimp only
  intro p z hz
  let U : ℝ≥0 × Ω → ℝ := fun p =>
    let y := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    if y ∈ Icc l u then y else l
  let A : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
  have hU : U p ∈ Icc l u := by
    dsimp [U]
    split_ifs with h
    · exact h
    · exact ⟨le_rfl, hlu.le⟩
  have hA0 : 0 ≤ A p := by
    dsimp [A]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hA1 : A p ≤ 1 := by
    dsimp [A]
    split_ifs
    · have ht : 0 ≤ (p.1 : ℝ) := p.1.property
      have hmul : 0 ≤ q * (p.1 : ℝ) := mul_nonneg hq ht
      exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr hmul)
    · norm_num
  have hTaylor := hbound (U p) hU z hz
  change |A p * SpectrallyNegativeLevy.generatorIntegrand f (U p) z| ≤
    C * z ^ 2
  rw [abs_mul, abs_of_nonneg hA0]
  calc
    A p * |SpectrallyNegativeLevy.generatorIntegrand f (U p) z| ≤
        |SpectrallyNegativeLevy.generatorIntegrand f (U p) z| := by
      nlinarith [abs_nonneg (SpectrallyNegativeLevy.generatorIntegrand f (U p) z)]
    _ ≤ C * z ^ 2 := by
      simpa [Real.norm_eq_abs] using hTaylor
