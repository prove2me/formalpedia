-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_joint_exp_clock_rate_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:09:25.290008+00:00
-- url     : https://prove2.me/submissions/e1fbe161-f9c4-4f94-bbc3-721fda877c61

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_discount_rate_shift_lintegral_ws01a

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal

/-- A genuine path-clock product integral changes rate after an exponential discount. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (A : Ω × ℝ → ℝ≥0∞) (hA : Measurable A) :
    ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-(q * z.2))) * A z
        ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, A z
        ∂(P.prod (ProbabilityTheory.expMeasure (p + q)))) := by
  have hr : 0 < p + q := by linarith
  let g : ℝ → ℝ≥0∞ := fun t => ∫⁻ ω : Ω, A (ω, t) ∂P
  have hg : Measurable g := hA.lintegral_prod_left'
  have hExp : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (-(q * z.2)))) :=
    (Real.continuous_exp.measurable.comp
      ((measurable_const.mul measurable_snd).neg)).ennreal_ofReal
  have hDiscount : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (-(q * z.2))) * A z) :=
    hExp.mul hA
  have hP := chat04_exponential_clock_killed_reward_tonelli
    P p hp Set.univ MeasurableSet.univ _ hDiscount
  have hR := chat04_exponential_clock_killed_reward_tonelli
    P (p + q) hr Set.univ MeasurableSet.univ A hA
  simp at hP hR
  have hInner (t : ℝ) :
      (∫⁻ ω : Ω, ENNReal.ofReal (Real.exp (-(q * t))) *
        A (ω, t) ∂P) =
      ENNReal.ofReal (Real.exp (-(q * t))) * g t := by
    dsimp [g]
    rw [lintegral_const_mul]
    exact hA.comp (measurable_id.prodMk measurable_const)
  calc
    _ = ENNReal.ofReal (p + q) *
        (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
          (ENNReal.ofReal (Real.exp (-(q * t))) * g t) ∂volume) := by
      rw [hP]
      congr 1
      apply lintegral_congr
      intro t
      rw [hInner t]
    _ = ENNReal.ofReal (p + q) *
        (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
          ENNReal.ofReal (Real.exp (-(q * t))) * g t ∂volume) := by
      congr 1
      apply lintegral_congr
      intro t
      ac_rfl
    _ = ENNReal.ofReal p *
        (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF (p + q) t *
          g t ∂volume) :=
      chat04_exponential_discount_rate_shift_lintegral_ws01a p q hp hq g hg
    _ = _ := by rw [hR]
