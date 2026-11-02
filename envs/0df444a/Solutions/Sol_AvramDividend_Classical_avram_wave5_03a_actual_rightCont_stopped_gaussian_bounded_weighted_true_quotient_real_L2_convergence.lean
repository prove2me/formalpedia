-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_quotient_real_L2_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:13:06.980708+00:00
-- url     : https://prove2.me/submissions/67911842-caae-4229-96d8-6bd1d6f5c03c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Genuine bounded stopped-gradient multiplication preserves source L2 convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun θ : ℝ => (∫ ω, (H ω * (Z θ ω - Y ω)) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  dsimp only
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change Filter.Tendsto
    (fun θ : ℝ => (∫ ω, (H ω * (Z θ ω - Y ω)) ^ 2 ∂P))
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
  have hCauchy : Filter.Tendsto
      (fun θ : ℝ => (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
      X hν τ hτ T hbounded h
  have hscale : Filter.Tendsto
      (fun θ : ℝ => K ^ 2 * (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hCauchy.const_mul (K ^ 2)
  have hnonneg : ∀ θ : ℝ,
      0 ≤ (∫ ω, (H ω * (Z θ ω - Y ω)) ^ 2 ∂P) := by
    intro θ
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hupper : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ),
      (∫ ω, (H ω * (Z θ ω - Y ω)) ^ 2 ∂P) ≤
        K ^ 2 * (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P) := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hMemθ : MemLp (Z θ) 2 P :=
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
        X hν τ hτ T hbounded h θ
        (le_of_lt (Set.mem_Ioi.mp hθ))).1
    have hMemY : MemLp Y 2 P := by
      simpa only [Y] using
        avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
          X hν τ hτ T hbounded h
    have hMemΔ : MemLp (fun ω => Z θ ω - Y ω) 2 P :=
      hMemθ.sub hMemY
    have hSq : Integrable (fun ω => (Z θ ω - Y ω) ^ 2) P :=
      (memLp_two_iff_integrable_sq hMemΔ.aestronglyMeasurable).mp hMemΔ
    have hTop : Integrable (fun ω => K ^ 2 * (Z θ ω - Y ω) ^ 2) P :=
      hSq.const_mul (K ^ 2)
    have hpoint (ω : Ω) :
        (H ω * (Z θ ω - Y ω)) ^ 2 ≤
        K ^ 2 * (Z θ ω - Y ω) ^ 2 := by
      have hHa := abs_le.mp (hH ω)
      have hsq : (H ω) ^ 2 ≤ K ^ 2 := by
        have hp : 0 ≤ (K - H ω) * (K + H ω) :=
          mul_nonneg (sub_nonneg.mpr hHa.2) (by linarith)
        nlinarith
      calc
        _ = (H ω) ^ 2 * (Z θ ω - Y ω) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    calc
      (∫ ω, (H ω * (Z θ ω - Y ω)) ^ 2 ∂P) ≤
          (∫ ω, K ^ 2 * (Z θ ω - Y ω) ^ 2 ∂P) := by
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
          hTop
          (Filter.Eventually.of_forall hpoint)
      _ = K ^ 2 * (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P) := by
        rw [integral_const_mul]
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hupper hscale
