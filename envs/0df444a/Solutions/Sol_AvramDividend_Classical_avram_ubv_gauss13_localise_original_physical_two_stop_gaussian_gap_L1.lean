-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:31:44.937196+00:00
-- url     : https://prove2.me/submissions/0662ce04-3295-479c-befb-dd0c2ed0df02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ ρ : Ω → ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (ε : ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hS : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (s n ω) ω - (s n ω : ℝ) * X.c)
        atTop (𝓝 (X.X (τ ω) ω - (τ ω : ℝ) * X.c)))
    (hT : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (t n ω) ω - (t n ω : ℝ) * X.c)
        atTop (𝓝 (X.X (ρ ω) ω - (ρ ω : ℝ) * X.c)))
    (hMeas : ∀ n, Measurable (fun ω : Ω =>
      ENNReal.ofReal (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
        (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2)))
    (hSampleBound : ∀ n,
      (∫⁻ ω, ENNReal.ofReal
        (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
          (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2) ∂P) ≤
        ENNReal.ofReal (((ε : ℝ) + (δ n : ℝ)) * X.σ ^ 2)) :
    (∫⁻ ω, (ENNReal.ofReal
      (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) ^ 2)) ^ (1 / 2 : ℝ) ∂P) ≤
      (ENNReal.ofReal ((ε : ℝ) * X.σ ^ 2)) ^ (1 / 2 : ℝ) := by
  let A : ℕ → Ω → ℝ := fun n ω => X.X (s n ω) ω - (s n ω : ℝ) * X.c
  let B : ℕ → Ω → ℝ := fun n ω => X.X (t n ω) ω - (t n ω : ℝ) * X.c
  let L : Ω → ℝ := fun ω => X.X (τ ω) ω - (τ ω : ℝ) * X.c
  let U : Ω → ℝ := fun ω => X.X (ρ ω) ω - (ρ ω : ℝ) * X.c
  let G : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ((U ω - L ω) ^ 2)
  have hGMeas : AEMeasurable G P := by
    apply ENNReal.aemeasurable_of_tendsto
      (f := fun n ω => ENNReal.ofReal ((B n ω - A n ω) ^ 2))
    · intro n
      exact (hMeas n).aemeasurable
    · filter_upwards [hS, hT] with ω hs ht
      have hSub : Tendsto (fun n => B n ω - A n ω) atTop
          (𝓝 (U ω - L ω)) := ht.sub hs
      exact (ENNReal.continuous_ofReal.tendsto ((U ω - L ω) ^ 2)).comp (hSub.pow 2)
  have hEnergy : (∫⁻ ω, G ω ∂P) ≤
      ENNReal.ofReal ((ε : ℝ) * X.σ ^ 2) :=
    avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L2
      X hν τ ρ s t ε δ hδ hS hT hMeas hSampleBound
  have hHolder : (∫⁻ ω, (G ω) ^ (1 / 2 : ℝ) ∂P) ≤
      (∫⁻ ω, G ω ∂P) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_norm_pow_le
      hGMeas (aemeasurable_const : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simpa only [ENNReal.one_rpow, mul_one, lintegral_const, measure_univ,
      one_pow] using h
  exact hHolder.trans (ENNReal.rpow_le_rpow hEnergy (by norm_num))
