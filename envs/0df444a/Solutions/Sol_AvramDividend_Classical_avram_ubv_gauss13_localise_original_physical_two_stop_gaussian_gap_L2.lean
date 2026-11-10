-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:38:07.843275+00:00
-- url     : https://prove2.me/submissions/8d4451aa-3890-4730-947a-caedb8bb158d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_two_clock_physical_energy_fatou

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    (∫⁻ ω, ENNReal.ofReal
      (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) ^ 2) ∂P) ≤
      ENNReal.ofReal ((ε : ℝ) * X.σ ^ 2) := by
  have hFatou :=
    avram_ubv_gauss13_localise_original_two_clock_physical_energy_fatou
      X hν τ ρ s t hS hT hMeas
  have hDeltaReal : Tendsto (fun n => (δ n : ℝ)) atTop
      (𝓝 (0 : ℝ)) :=
    (NNReal.continuous_coe.tendsto 0).comp hδ
  have hConst : Tendsto (fun _ : ℕ => (ε : ℝ)) atTop
      (𝓝 (ε : ℝ)) := tendsto_const_nhds
  have hBoundReal : Tendsto
      (fun n => ((ε : ℝ) + (δ n : ℝ)) * X.σ ^ 2) atTop
      (𝓝 ((ε : ℝ) * X.σ ^ 2)) := by
    have h := (hConst.add hDeltaReal).mul_const (X.σ ^ 2)
    simpa only [add_zero] using h
  have hBoundTendsto : Tendsto
      (fun n => ENNReal.ofReal
        (((ε : ℝ) + (δ n : ℝ)) * X.σ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal ((ε : ℝ) * X.σ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto ((ε : ℝ) * X.σ ^ 2)).comp hBoundReal
  calc
    (∫⁻ ω, ENNReal.ofReal
      (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) ^ 2) ∂P) ≤
      Filter.liminf (fun n =>
        ∫⁻ ω, ENNReal.ofReal
          (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
            (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2) ∂P)
      atTop := hFatou
    _ ≤ Filter.liminf
        (fun n => ENNReal.ofReal
          (((ε : ℝ) + (δ n : ℝ)) * X.σ ^ 2)) atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall hSampleBound)
    _ = ENNReal.ofReal ((ε : ℝ) * X.σ ^ 2) :=
      hBoundTendsto.liminf_eq
