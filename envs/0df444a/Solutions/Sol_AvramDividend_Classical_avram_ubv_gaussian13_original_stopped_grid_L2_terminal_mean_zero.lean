-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian13_original_stopped_grid_L2_terminal_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:47:36.743381+00:00
-- url     : https://prove2.me/submissions/a6b8be21-3a3f-4612-822b-5f393f9633f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_zero_nu_original_bounded_stopped_gaussian_grid_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The L² limit of genuinely stopped, bounded predictable Gaussian sums on
the original no-jump Lévy space is L² and has zero expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n i, i ∈ S n → ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hB : ∀ n i, i ∈ S n → ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGstop : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events
        (τ n i) (hτ n i hi)).measurableSpace] (G n i))
    (hGglobal : ∀ n i, i ∈ S n → Measurable (G n i))
    (K : ℕ → ι → ℝ) (hK : ∀ n i, i ∈ S n → 0 ≤ K n i)
    (hGbound : ∀ n i, i ∈ S n → ∀ ω, |G n i ω| ≤ K n i)
    (M : Ω → ℝ) (hMmeas : AEStronglyMeasurable M P) :
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω *
        (X.X (τ n i ω + h n i) ω - X.X (τ n i ω) ω -
          (h n i : ℝ) * X.c)
    (∀ n, MemLp (Q n) 2 P) →
    Tendsto (fun n => eLpNorm (Q n - M) 2 P) atTop (𝓝 0) →
    MemLp M 2 P ∧ (∫ ω, M ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n, G n i ω *
      (X.X (τ n i ω + h n i) ω - X.X (τ n i ω) ω -
        (h n i : ℝ) * X.c)
  change (∀ n, MemLp (Q n) 2 P) →
    Tendsto (fun n => eLpNorm (Q n - M) 2 P) atTop (𝓝 0) →
    MemLp M 2 P ∧ (∫ ω, M ω ∂P) = 0
  intro hQ2 hL2
  have hQzero (n : ℕ) : (∫ ω, Q n ω ∂P) = 0 :=
    (avram_ubv_loc6_zero_nu_original_bounded_stopped_gaussian_grid_mean_zero
      X hν (S n) (τ n) (hτ n) (B n) (hB n)
      (h n) (G n) (hGstop n) (hGglobal n)
      (K n) (hK n) (hGbound n)).2
  have hM2 : MemLp M 2 P :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) hQ2 M hMmeas hL2
  have hL1bound (n : ℕ) :
      eLpNorm (Q n - M) 1 P ≤ eLpNorm (Q n - M) 2 P :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((hQ2 n).aestronglyMeasurable.sub hM2.aestronglyMeasurable)
  have hL1 :
      Tendsto (fun n => eLpNorm (Q n - M) 1 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL2
      (fun _ => zero_le) hL1bound
  have hInt := tendsto_integral_of_L1' M hM2.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun n => (hQ2 n).integrable (by norm_num))) hL1
  refine ⟨hM2, ?_⟩
  exact tendsto_nhds_unique hInt (by
    simpa only [hQzero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
