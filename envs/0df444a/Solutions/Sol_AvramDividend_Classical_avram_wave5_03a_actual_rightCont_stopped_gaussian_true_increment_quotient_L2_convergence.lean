-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_L2_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:56:42.196134+00:00
-- url     : https://prove2.me/submissions/b579e834-415a-4cc0-a862-e3607afcaee8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_fatou_error_le
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
      (fun θ : ℝ => (∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  let a : ℝ := (h : ℝ) * X.σ ^ 2
  let E : ℝ → ℝ≥0∞ := fun θ =>
    ∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P
  change Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))
  have hid :
      Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsq0 :
      Tendsto (fun θ : ℝ => θ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hid.pow 2
  have hsq :
      Tendsto (fun θ : ℝ => θ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hsq0
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact pow_pos (show (0 : ℝ) < θ from hθ) 2
  have hsec :
      Tendsto (fun ε : ℝ => (Real.exp (a * ε) - 1) / ε)
        (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    simpa only [zero_mul, add_zero] using
      (avram_wave5_03a_exp_quadratic_secant_right_limit a 0)
  have hR :
      Tendsto (fun θ : ℝ =>
        ((Real.exp (a * θ ^ 2) - 1) / θ ^ 2) - a)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have ht := (hsec.comp hsq).sub_const a
    change Tendsto (fun θ : ℝ =>
      ((Real.exp (a * θ ^ 2) - 1) / θ ^ 2) - a)
      (𝓝[>] (0 : ℝ)) (𝓝 (a - a)) at ht
    simpa only [sub_self] using ht
  have hRE :
      Tendsto (fun θ : ℝ => ENNReal.ofReal
        (((Real.exp (a * θ ^ 2) - 1) / θ ^ 2) - a))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have ht := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hR
    change Tendsto (fun θ : ℝ => ENNReal.ofReal
      (((Real.exp (a * θ ^ 2) - 1) / θ ^ 2) - a))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (0 : ℝ))) at ht
    simpa only [ENNReal.ofReal_zero] using ht
  have hUpper :
      ∀ᶠ θ : ℝ in (𝓝[>] (0 : ℝ)),
        E θ ≤ ENNReal.ofReal
          (((Real.exp (a * θ ^ 2) - 1) / θ ^ 2) - a) := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    simpa only [E, Y, Z, a, mul_assoc] using
      (avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_fatou_error_le
        X hν τ hτ T hbounded h θ hθ)
  have hLower :
      ∀ᶠ θ : ℝ in (𝓝[>] (0 : ℝ)), (0 : ℝ≥0∞) ≤ E θ :=
    Filter.Eventually.of_forall (fun θ => bot_le)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hRE hLower hUpper
