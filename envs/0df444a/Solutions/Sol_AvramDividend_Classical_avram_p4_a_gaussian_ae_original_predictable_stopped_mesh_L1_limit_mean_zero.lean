-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_predictable_stopped_mesh_L1_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:49:09.688546+00:00
-- url     : https://prove2.me/submissions/33c9d561-4b12-4867-9f5a-55c0170ccf6d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_full_taylor_L1_sum_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

/-- An L1 limit of original-source stopped Gaussian Taylor meshes has mean zero.
This uses precisely the source-centred continuous remainder, original filtration,
and the Gaussian variance of X. Existence of the decomposition and L1 limit
remain explicit hypotheses, including when X has no Brownian part. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hGstopped : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i) (hτ n i hi)).measurableSpace]
        (G n i))
    (hHstopped : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i) (hτ n i hi)).measurableSpace]
        (H n i))
    (hGglobal : ∀ n, ∀ i ∈ S n, Measurable (G n i))
    (hHglobal : ∀ n, ∀ i ∈ S n, Measurable (H n i))
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : ∀ u ω, Z u ω =
      X.X u ω - (u : ℝ) * X.c - Jsmall u ω - Jlarge u ω)
    (hGI : ∀ n, ∀ i ∈ S n, Integrable (fun ω => G n i ω *
      (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω)) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n, Integrable (fun ω => H n i ω *
      (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) ^ 2) P)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ n ω, F n ω = ∑ i ∈ S n,
        (G n i ω * (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) +
        (1 / 2 : ℝ) * H n i ω *
          ((Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) ^ 2 -
            (h n i : ℝ) * X.σ ^ 2)))
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖F n ω - f ω‖ₑ ∂P)
      atTop (nhds 0)) :
    (∫ ω, f ω ∂P) = 0 := by
  have hMesh (n : ℕ) : Integrable (F n) P ∧ (∫ ω, F n ω ∂P) = 0 := by
    have hFin :=
      avram_p4_a_gaussian_ae_original_variable_stopped_predictable_full_taylor_L1_sum_mean_zero
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        (S n) (τ n) (hτ n) (B n) (hbounded n) (h n)
        (G n) (H n) (hGstopped n) (hHstopped n)
        (hGglobal n) (hHglobal n)
        (by simpa only [hZ, NNReal.coe_add] using hGI n)
        (hHI n)
        (by simpa only [hZ, NNReal.coe_add] using hH2I n)
    have hEq : F n = (fun ω =>
        ∑ i ∈ S n,
          (G n i ω *
            ((X.X (τ n i ω + h n i) ω -
              ((τ n i ω + h n i) : ℝ) * X.c -
              Jsmall (τ n i ω + h n i) ω - Jlarge (τ n i ω + h n i) ω) -
             (X.X (τ n i ω) ω - (τ n i ω : ℝ) * X.c -
              Jsmall (τ n i ω) ω - Jlarge (τ n i ω) ω)) +
          (1 / 2 : ℝ) * H n i ω *
            (((X.X (τ n i ω + h n i) ω -
                ((τ n i ω + h n i) : ℝ) * X.c -
                Jsmall (τ n i ω + h n i) ω - Jlarge (τ n i ω + h n i) ω) -
               (X.X (τ n i ω) ω - (τ n i ω : ℝ) * X.c -
                Jsmall (τ n i ω) ω - Jlarge (τ n i ω) ω)) ^ 2 -
              (h n i : ℝ) * X.σ ^ 2))) := by
      funext ω
      rw [hF]
      simp only [hZ, NNReal.coe_add]
    rw [hEq]
    exact hFin
  exact avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
    P F f hf (fun n => (hMesh n).1) (fun n => (hMesh n).2) hL1
