-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:03:03.261645+00:00
-- url     : https://prove2.me/submissions/ae270391-d0b9-4a32-ad75-9348b365cfdd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_L2_convergence
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

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
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun θ : ℝ => (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change Filter.Tendsto
    (fun θ : ℝ => ∫ ω, (Z θ ω - Y ω) ^ 2 ∂P)
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
  have hYmem : MemLp Y 2 P := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν τ hτ T hbounded h
  have hZmem (θ : ℝ) (hθ : 0 ≤ θ) : MemLp (Z θ) 2 P := by
    simpa only [Z] using
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
        X hν τ hτ T hbounded h θ hθ).1
  have hI (θ : ℝ) (hθ : 0 ≤ θ) :
      (∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P) =
      ENNReal.ofReal (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P) := by
    have hm : MemLp (fun ω => Z θ ω - Y ω) 2 P :=
      (hZmem θ hθ).sub hYmem
    have hs : Integrable (fun ω => (Z θ ω - Y ω) ^ 2) P :=
      (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
    exact (ofReal_integral_eq_lintegral_ofReal hs
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))).symm
  have hE : Filter.Tendsto
      (fun θ : ℝ => ∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Y, Z] using
      (avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_L2_convergence
        X hν τ hτ T hbounded h)
  have hToReal : Filter.Tendsto
      (fun θ : ℝ =>
        (∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have ht :=
      ((ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto).comp hE
    change Filter.Tendsto
      (fun θ : ℝ =>
        (∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ≥0∞).toReal)) at ht
    simpa only [ENNReal.toReal_zero] using ht
  apply hToReal.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  rw [hI θ (le_of_lt (Set.mem_Ioi.mp hθ))]
  exact ENNReal.toReal_ofReal
    (integral_nonneg (fun ω => sq_nonneg (Z θ ω - Y ω)))
