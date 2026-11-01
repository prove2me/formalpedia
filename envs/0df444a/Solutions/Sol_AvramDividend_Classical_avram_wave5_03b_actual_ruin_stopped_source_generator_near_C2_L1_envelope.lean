-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:27:33.323615+00:00
-- url     : https://prove2.me/submissions/a01fd870-2cfb-48ab-8948-efc1ecb4eaec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual ruin-stopped prepayment Taylor remainder is O(z²) on a compact
interior reserve band, using the genuine source generator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u + δ) (huv : u + δ < v) (hv : v < C) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    ∃ r M : ℝ, 0 < r ∧ r ≤ min (u + δ) 1 ∧ 0 ≤ M ∧
      ∀ p : ℝ≥0 × Ω, Y p ∈ Icc (u + δ) v →
        ∀ z ∈ Ioo (-r) 0, |HS (p,z)| ≤ M * z ^ 2 := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  change ∃ r M : ℝ, 0 < r ∧ r ≤ min (u + δ) 1 ∧ 0 ≤ M ∧
      ∀ p : ℝ≥0 × Ω, Y p ∈ Icc (u + δ) v →
        ∀ z ∈ Ioo (-r) 0, |HS (p,z)| ≤ M * z ^ 2
  obtain ⟨r, M, hr, hrle, hM, hpoint⟩ :=
    avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
      X w C (u + δ) v hu huv hv hw
  refine ⟨r, M, hr, hrle, hM, ?_⟩
  intro p hp z hz
  have hzneg : z < 0 := hz.2
  have hid :=
    avram_wave5_03b_actual_source_taylor_generator_kernel_eq
      X x D hD w u v δ p z hzneg
  change H (p,z) =
    if Y p ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0 at hid
  have hH : |H (p,z)| ≤ M * z ^ 2 := by
    rw [hid, if_pos hp]
    exact hpoint (Y p) hp z hz
  by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
  · simpa [HS, hs] using hH
  · simpa [HS, hs] using (mul_nonneg hM (sq_nonneg z))
