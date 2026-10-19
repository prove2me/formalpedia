-- Prove2me | solution 1 for FastCLO.LowerBound.jensen_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:40:16.549443+00:00
-- url     : https://prove2.me/submissions/41040c61-c8db-465f-8402-3c3465c3d6fe

import Mathlib

set_option autoImplicit false

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 1 ≤ c) (N : Ω → ℝ) (hN : Measurable N) (hN0 : ∀ ω, 0 ≤ N ω)
    (hint : Integrable N Q) :
    (1 / 2) * c ^ (-(∫ ω, N ω ∂Q)) ≤ ∫ ω, (1 + c ^ N ω)⁻¹ ∂Q := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  set L : ℝ := Real.log c with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hc
  have hpow : ∀ x : ℝ, c ^ x = Real.exp (L * x) := fun x => Real.rpow_def_of_pos hc0 x
  -- convexity of g t = exp(-L t)
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Real.exp (-L * t)) := by
    have h := convexOn_exp.comp_linearMap ((-L) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    simpa [Function.comp_def] using h
  have hcont : Continuous (fun t : ℝ => Real.exp (-L * t)) := by fun_prop
  have hmeas : Measurable (fun ω => Real.exp (-L * N ω)) := by fun_prop
  have hint1 : Integrable (fun ω => Real.exp (-L * N ω)) Q := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hN0 ω]
  have hjensen := hconv.map_integral_le hcont.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hint hint1
  have hmeas2 : Measurable (fun ω => (1 + c ^ N ω)⁻¹) := by
    have : Measurable (fun ω => c ^ N ω) := by
      simp_rw [hpow]; fun_prop
    fun_prop
  have hint2 : Integrable (fun ω => (1 + c ^ N ω)⁻¹) Q := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas2.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : 1 ≤ c ^ N ω := Real.one_le_rpow hc (hN0 ω)
    have hp : 0 < (1 + c ^ N ω)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_pos hp]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hpt : ∀ ω, (1 / 2) * Real.exp (-L * N ω) ≤ (1 + c ^ N ω)⁻¹ := by
    intro ω
    have h1 : 1 ≤ c ^ N ω := Real.one_le_rpow hc (hN0 ω)
    have he : Real.exp (-L * N ω) = (c ^ N ω)⁻¹ := by
      rw [hpow, ← Real.exp_neg]; ring_nf
    rw [he]
    have hp : 0 < c ^ N ω := by linarith
    rw [← one_div, ← one_div, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hmono : ∫ ω, (1 / 2) * Real.exp (-L * N ω) ∂Q ≤ ∫ ω, (1 + c ^ N ω)⁻¹ ∂Q :=
    integral_mono (hint1.const_mul _) hint2 hpt
  rw [integral_const_mul] at hmono
  have : c ^ (-(∫ ω, N ω ∂Q)) = Real.exp (-L * ∫ ω, N ω ∂Q) := by
    rw [hpow]; ring_nf
  rw [this]
  have hj : Real.exp (-L * ∫ ω, N ω ∂Q) ≤ ∫ ω, Real.exp (-L * N ω) ∂Q := hjensen
  linarith
