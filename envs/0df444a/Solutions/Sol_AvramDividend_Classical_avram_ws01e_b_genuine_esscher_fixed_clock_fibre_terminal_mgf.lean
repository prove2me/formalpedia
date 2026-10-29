-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_genuine_esscher_fixed_clock_fibre_terminal_mgf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T20:45:29.180389+00:00
-- url     : https://prove2.me/submissions/e50b006b-0bab-40c1-a681-31171bd2078b

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q β : ℝ) (hroot : X.ψ φ = q)
    (hθ : 0 ≤ φ + β) (t : ℝ) :
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp
        (φ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ φ)) *
      ENNReal.ofReal (Real.exp
        (β * X.X (Real.toNNReal t) ω)) ∂P) =
    ENNReal.ofReal (Real.exp
      ((Real.toNNReal t : ℝ) * (X.ψ (φ + β) - q))) := by
  let u : ℝ≥0 := Real.toNNReal t
  have hi := X.laplace u (φ + β) hθ
  have hMoment :
      (∫⁻ ω : Ω, ENNReal.ofReal
        (Real.exp ((φ + β) * X.X u ω)) ∂P) =
      ENNReal.ofReal (Real.exp ((u : ℝ) * X.ψ (φ + β))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1
      (Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _)))]
    exact congrArg ENNReal.ofReal hi.2
  have hPoint (ω : Ω) :
      ENNReal.ofReal (Real.exp
        (φ * X.X u ω - (u : ℝ) * X.ψ φ)) *
      ENNReal.ofReal (Real.exp (β * X.X u ω)) =
      ENNReal.ofReal (Real.exp (-(u : ℝ) * q)) *
        ENNReal.ofReal (Real.exp ((φ + β) * X.X u ω)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [← Real.exp_add, ← Real.exp_add, hroot]
    ring
  change (∫⁻ ω : Ω,
    ENNReal.ofReal (Real.exp (φ * X.X u ω - (u : ℝ) * X.ψ φ)) *
    ENNReal.ofReal (Real.exp (β * X.X u ω)) ∂P) =
    ENNReal.ofReal (Real.exp ((u : ℝ) * (X.ψ (φ + β) - q)))
  calc
    _ = ∫⁻ ω : Ω,
        ENNReal.ofReal (Real.exp (-(u : ℝ) * q)) *
          ENNReal.ofReal (Real.exp ((φ + β) * X.X u ω)) ∂P := by
      apply lintegral_congr
      exact hPoint
    _ = ENNReal.ofReal (Real.exp (-(u : ℝ) * q)) *
          (∫⁻ ω : Ω,
            ENNReal.ofReal (Real.exp ((φ + β) * X.X u ω)) ∂P) := by
      rw [lintegral_const_mul]
      exact ENNReal.measurable_ofReal.comp
        (Real.continuous_exp.measurable.comp
          (measurable_const.mul
            ((chat04_levy_joint_time_state_measurable X).comp
              (measurable_const.prodMk measurable_id))))
    _ = ENNReal.ofReal (Real.exp ((u : ℝ) *
          (X.ψ (φ + β) - q))) := by
      rw [hMoment, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← Real.exp_add]
      congr 1
      ring
