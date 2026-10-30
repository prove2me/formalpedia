-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:44:21.057276+00:00
-- url     : https://prove2.me/submissions/236c3a2e-8a1b-434f-bf2c-08a9c94ee5ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_clock_marginal_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Under the genuine terminal Esscher law, an observation beyond the
finite cap has exactly the original Exp(p) tail, regardless of the path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (N : ℝ≥0) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     Qp {z : Ω × ℝ | (N : ℝ) < z.2} =
       ENNReal.ofReal (Real.exp (-(p * (N : ℝ))))) := by
  intro Qp
  have hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))) := by
    have hX := chat04_levy_joint_time_state_measurable X
    have hT : Measurable (fun z : Ω × ℝ =>
        Real.toNNReal z.2) := by fun_prop
    have hXT : Measurable (fun z : Ω × ℝ =>
        X.X (Real.toNNReal z.2) z.1) :=
      hX.comp (hT.prodMk measurable_fst)
    fun_prop
  have hMarg :=
    chat04_esscher_joint_exponential_clock_marginal_of_measurable_likelihood
      X θ p hθ hp hJoint
  have hTail : Qp {z : Ω × ℝ | (N : ℝ) < z.2} =
      (expMeasure p) (Set.Ioi (N : ℝ)) := by
    have hm := congrArg (fun μ : Measure ℝ => μ (Set.Ioi (N : ℝ))) hMarg
    rw [Measure.map_apply measurable_snd measurableSet_Ioi] at hm
    change Qp {z : Ω × ℝ | (N : ℝ) < z.2} =
      (expMeasure p) (Set.Ioi (N : ℝ)) at hm
    exact hm
  rw [hTail]
  exact avram_ws01e_b_expMeasure_strict_survival_real
    p N hp (NNReal.coe_nonneg N)
