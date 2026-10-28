-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_discounted_killed_exponential_reflected_pair_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:01:24.751616+00:00
-- url     : https://prove2.me/submissions/49b330d4-aa59-4f0e-91ad-62bdb2957097

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_discount_rate_shift_lintegral_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

/-- Independent-clock discounting changes the exponential rate, on the
    genuine product path/clock probability measure. -/
private theorem product_exp_rate_shift_ws01a
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

/-- Genuine discounted killed reward as an action of the actual reflected-pair
    pushforward law. This does not assume Wiener–Hopf independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-(q * z.2))) *
          (if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
           then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
           else (0 : ℝ≥0∞))
        ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    ENNReal.ofReal p *
      (∫⁻ a : ℝ × ℝ,
        if a.1 ≤ x then ENNReal.ofReal (W (x - a.1 + a.2))
        else (0 : ℝ≥0∞)
        ∂((P.prod (ProbabilityTheory.expMeasure (p + q))).map
          (fun z : Ω × ℝ =>
            (-sInf {y : ℝ | ∃ s : ℝ≥0,
                      s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1},
             X.X (Real.toNNReal z.2) z.1 +
               -sInf {y : ℝ | ∃ s : ℝ≥0,
                         s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})))) := by
  let A : Ω × ℝ → ℝ≥0∞ := fun z =>
    if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
    then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
    else 0
  have hr : 0 < p + q := by linarith
  have hTime : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hInf : Measurable (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) := by
    simpa [Function.comp_def] using
      (levy_running_infimum_joint_time_path_measurable X).comp hTime
  have hXt : Measurable (fun z : Ω × ℝ =>
      X.X (Real.toNNReal z.2) z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hTime
  have hSurv : MeasurableSet
      {z : Ω × ℝ |
        ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1} := by
    have hSet :
        {z : Ω × ℝ |
          ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1} =
        {z : Ω × ℝ |
          -sInf {y : ℝ | ∃ s : ℝ≥0,
            s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x} := by
      ext z
      exact (chat04_reflected_infimum_Iic_iff_survival X
        (Real.toNNReal z.2) z.1 x).symm
    rw [hSet]
    exact measurableSet_Iic.preimage hInf
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hPay : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))) :=
    ENNReal.measurable_ofReal.comp
      (hWm.comp (measurable_const.add hXt))
  have hA : Measurable A :=
    Measurable.ite hSurv hPay measurable_const
  have hShift := product_exp_rate_shift_ws01a P p q hp hq A hA
  have hPair :=
    chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
      P X (p + q) hr x q W hW
  calc
    _ = ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, A z
        ∂(P.prod (ProbabilityTheory.expMeasure (p + q)))) := by
      simpa only [A] using hShift
    _ = _ := by rw [hPair]

