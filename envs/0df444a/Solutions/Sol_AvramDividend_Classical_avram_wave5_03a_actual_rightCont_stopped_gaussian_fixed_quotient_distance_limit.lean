-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_distance_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:18:24.867884+00:00
-- url     : https://prove2.me/submissions/2d2062e9-da5e-4d0c-a789-31f2cadfd089

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_fixed_parameter_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_quotient_L2_distance_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_quadratic_secant_right_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun ε : ℝ => (∫ ω,
        (Z θ ω - Z (Real.sqrt ε) ω) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) /
        θ ^ 2) - (h : ℝ) * X.σ ^ 2)) := by
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  let a : ℝ := (h : ℝ) * X.σ ^ 2
  let E : ℝ → ℝ := fun η =>
    (Real.exp ((h : ℝ) * (X.σ ^ 2 * η ^ 2)) - 1) / η ^ 2
  let C : ℝ → ℝ := fun η =>
    (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η)
  change Filter.Tendsto
    (fun ε : ℝ => ∫ ω, (Z θ ω - Z (Real.sqrt ε) ω) ^ 2 ∂P)
    (𝓝[>] (0 : ℝ)) (𝓝 (E θ - a))
  have hnear : Filter.Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [id_eq, Real.sqrt_zero] using
      ((tendsto_id.mono_left nhdsWithin_le_nhds).sqrt :
        Filter.Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)))
  have hsqrt : Filter.Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hnear
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Real.sqrt_pos.2 hε
  have hE : Filter.Tendsto (fun ε : ℝ => E (Real.sqrt ε))
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    apply (avram_wave5_03a_exp_quadratic_secant_right_limit a 0).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    dsimp [E, a]
    rw [Real.sq_sqrt (le_of_lt hε)]
    simp only [zero_mul, add_zero]
    ring
  have hC : Filter.Tendsto (fun ε : ℝ => C (Real.sqrt ε))
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have hbase := (avram_wave5_03a_exp_quadratic_secant_right_limit (a * θ) 0).comp hsqrt
    have hdiv := hbase.div_const θ
    have hvalue : (a * θ) / θ = a := by
      field_simp [ne_of_gt hθ]
    rw [hvalue] at hdiv
    convert hdiv using 1
    funext ε
    dsimp [C, a]
    have harg : (h : ℝ) * (X.σ ^ 2 * θ * Real.sqrt ε) =
        ((h : ℝ) * X.σ ^ 2 * θ) * Real.sqrt ε := by ring
    rw [harg]
    simp only [zero_mul, add_zero, div_eq_mul_inv, mul_inv_rev]
    ring
  have hd (ε : ℝ) :
      (∫ ω, (Z θ ω - Z (Real.sqrt ε) ω) ^ 2 ∂P) =
        E θ + E (Real.sqrt ε) - 2 * C (Real.sqrt ε) := by
    simpa only [Z, E, C] using
      (avram_wave5_03a_actual_rightCont_stopped_gaussian_quotient_L2_distance_exact
        X hν τ hτ T hbounded h θ (Real.sqrt ε)
        (le_of_lt hθ) (Real.sqrt_nonneg ε))
  have hsum : Filter.Tendsto (fun ε : ℝ => E θ + E (Real.sqrt ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (E θ + a)) :=
    tendsto_const_nhds.add hE
  have hdouble : Filter.Tendsto (fun ε : ℝ => (2 : ℝ) * C (Real.sqrt ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * a)) :=
    tendsto_const_nhds.mul hC
  have hsub := hsum.sub hdouble
  have hlimit : Filter.Tendsto
      (fun ε : ℝ => E θ + E (Real.sqrt ε) - 2 * C (Real.sqrt ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (E θ - a)) := by
    convert hsub using 1 <;> ring
  exact hlimit.congr' (Filter.Eventually.of_forall fun ε => (hd ε).symm)
