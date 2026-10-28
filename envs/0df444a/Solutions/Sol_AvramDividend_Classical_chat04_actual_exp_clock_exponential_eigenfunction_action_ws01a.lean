-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_exp_clock_exponential_eigenfunction_action_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:07:26.440729+00:00
-- url     : https://prove2.me/submissions/99ccdae3-cf73-49aa-a7ec-37254b26b631

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The genuine path/independent-exponential-clock law acts on exponential test
functions through the actual Levy semigroup eigenvalue. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (θ * (x + X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (ProbabilityTheory.expMeasure r))) =
    (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
      ENNReal.ofReal (Real.exp (θ * x) *
        Real.exp ((Real.toNNReal t : ℝ) * X.ψ θ)) ∂volume) := by
  have hJoint := chat04_levy_joint_time_state_measurable X
  have hClock : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hXt : Measurable (fun z : Ω × ℝ =>
      X.X (Real.toNNReal z.2) z.1) := hJoint.comp hClock
  have hReward : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * (x + X.X (Real.toNNReal z.2) z.1)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (measurable_const.add hXt)))
  have hIntegrable (t : ℝ) :
      Integrable (fun ω : Ω => Real.exp
        (θ * (x + X.X (Real.toNNReal t) ω))) P := by
    have hi := (X.laplace (Real.toNNReal t) θ hθ).1
    have heq : (fun ω : Ω => Real.exp
        (θ * (x + X.X (Real.toNNReal t) ω))) =
        (fun ω : Ω => Real.exp (θ * x) *
          Real.exp (θ * X.X (Real.toNNReal t) ω)) := by
      funext ω
      rw [mul_add, Real.exp_add]
    rw [heq]
    exact hi.const_mul _
  have hInner (t : ℝ) :
      (∫⁻ ω : Ω, ENNReal.ofReal (Real.exp
        (θ * (x + X.X (Real.toNNReal t) ω))) ∂P) =
      ENNReal.ofReal (Real.exp (θ * x) *
        Real.exp ((Real.toNNReal t : ℝ) * X.ψ θ)) := by
    calc
      _ = ENNReal.ofReal (∫ ω : Ω,
            Real.exp (θ * (x + X.X (Real.toNNReal t) ω)) ∂P) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal (hIntegrable t)
          (Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _)))
      _ = _ := by
        rw [levy_transition_exponential_eigenfunction X
          (Real.toNNReal t) θ hθ x]
        rfl
  calc
    _ = (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
        (∫⁻ ω : Ω,
          ENNReal.ofReal (Real.exp
            (θ * (x + X.X (Real.toNNReal t) ω))) ∂P)
        ∂volume) := by
      simpa using
        (chat04_exponential_clock_killed_reward_tonelli P r hr
          (Set.univ : Set (Ω × ℝ)) MeasurableSet.univ _ hReward)
    _ = _ := by
      congr 1
      funext t
      rw [hInner t]
