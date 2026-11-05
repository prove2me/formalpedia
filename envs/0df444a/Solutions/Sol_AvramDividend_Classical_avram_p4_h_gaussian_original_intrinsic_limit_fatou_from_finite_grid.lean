-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_intrinsic_limit_fatou_from_finite_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:43:54.299847+00:00
-- url     : https://prove2.me/submissions/9b91ca46-f32a-4934-a268-494a8f8b9c36

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Fatou transfers uniform physical finite-grid jump energy to the actual
intrinsic original-process small-band compensated-jump difference.  The
almost-sure mesh limit and finite-grid second-moment bound are genuine
original-source obligations, rather than an independent Gaussian premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ)
    (G : ℕ → Ω → ℝ≥0∞)
    (hMeas : ∀ k, Measurable (G k))
    (hSourceLimit : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop
        (𝓝 (ENNReal.ofReal
          ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2))))
    (hSourceFiniteGrid : ∀ k,
      (∫⁻ ω, G k ω ∂P) ≤ (T : ℝ≥0∞) *
        (∫⁻ z in Ioc
          (-(1 / (((min n m : ℕ) : ℝ) + 1)))
          (-(1 / (((max n m : ℕ) : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν)) :
    (∫⁻ ω, ENNReal.ofReal
      ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) ∂P) ≤
      (T : ℝ≥0∞) *
        (∫⁻ z in Ioc
          (-(1 / (((min n m : ℕ) : ℝ) + 1)))
          (-(1 / (((max n m : ℕ) : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν) := by
  let cap : ℝ≥0∞ := (T : ℝ≥0∞) *
    (∫⁻ z in Ioc
      (-(1 / (((min n m : ℕ) : ℝ) + 1)))
      (-(1 / (((max n m : ℕ) : ℝ) + 1))),
      ENNReal.ofReal (z ^ 2) ∂X.ν)
  have hUniform (k : ℕ) : (∫⁻ ω, G k ω ∂P) ≤ cap :=
    hSourceFiniteGrid k
  have hLimitCap :
      liminf (fun k => ∫⁻ ω, G k ω ∂P) atTop ≤ cap := by
    have hMono :
        liminf (fun k => ∫⁻ ω, G k ω ∂P) atTop ≤
        liminf (fun _ : ℕ => cap) atTop :=
      Filter.liminf_le_liminf
        (Filter.Eventually.of_forall hUniform)
    simpa using hMono
  have hLiminf : ∀ᵐ ω ∂P,
      liminf (fun k => G k ω) atTop =
        ENNReal.ofReal
          ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) := by
    filter_upwards [hSourceLimit] with ω hω
    exact hω.liminf_eq
  change (∫⁻ ω, ENNReal.ofReal
    ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) ∂P) ≤
    cap
  calc
    (∫⁻ ω, ENNReal.ofReal
        ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) ∂P)
      = (∫⁻ ω, liminf (fun k => G k ω) atTop ∂P) :=
          lintegral_congr_ae (hLiminf.mono fun _ h => h.symm)
    _ ≤ liminf (fun k => ∫⁻ ω, G k ω ∂P) atTop :=
          lintegral_liminf_le hMeas
    _ ≤ cap := hLimitCap
