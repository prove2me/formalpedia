-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01h_true_Qp_strict_lower_killing_eq_closed_survival_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:16:54.626608+00:00
-- url     : https://prove2.me/submissions/f2b503b2-c492-4ab2-9f75-7d07e9e94ff5

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_true_strict_closed_exponential_product_integral_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Actual random-terminal Esscher Qp strict lower killing and closed-history
survival have equal integrals of every nonnegative measurable source reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (θ : ℝ) (x : ℝ)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator R z
       ∂Qp) =
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
           -x ≤ X.X s z.1}).indicator R z
       ∂Qp)) := by
  classical
  intro Qp
  let M : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))
  let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}
  let C : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
  have hE : MeasurableSet E :=
    chat04_exponential_clock_strict_lower_killing_joint_measurable X (-x)
  have hC : MeasurableSet C :=
    chat04_closed_history_lower_survival_joint_measurable_ws01a X x
  have hM : Measurable M := by
    have hX := chat04_levy_joint_time_state_measurable X
    have hu : Measurable
        (fun z : Ω × ℝ => Real.toNNReal z.2) := by fun_prop
    have hAt : Measurable
        (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) :=
      hX.comp (hu.prodMk measurable_fst)
    dsimp [M]
    fun_prop
  let G : Ω × ℝ → ℝ≥0∞ := fun z => M z * R z
  have hG : Measurable G := hM.mul hR
  have hER : Measurable (E.indicator R) := hR.indicator hE
  have hCR : Measurable (C.indicator R) := hR.indicator hC
  have hMain :=
    chat04_true_strict_closed_exponential_product_integral_ws01a
      P X p hp x G hG
  change (∫⁻ z, E.indicator R z ∂((P.prod (expMeasure p)).withDensity M)) =
    (∫⁻ z, C.indicator R z ∂((P.prod (expMeasure p)).withDensity M))
  rw [lintegral_withDensity_eq_lintegral_mul _ hM hER,
      lintegral_withDensity_eq_lintegral_mul _ hM hCR]
  have hSwap (S : Set (Ω × ℝ)) :
      (∫⁻ z, M z * S.indicator R z ∂(P.prod (expMeasure p))) =
      (∫⁻ z, S.indicator R z * M z ∂(P.prod (expMeasure p))) := by
    apply lintegral_congr
    intro z
    exact mul_comm _ _
  change (∫⁻ z, M z * E.indicator R z ∂(P.prod (expMeasure p))) =
    (∫⁻ z, M z * C.indicator R z ∂(P.prod (expMeasure p)))
  rw [hSwap E, hSwap C]
  calc
    (∫⁻ z, E.indicator R z * M z ∂(P.prod (expMeasure p))) =
        (∫⁻ z, E.indicator G z ∂(P.prod (expMeasure p))) := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ E <;> simp [Set.indicator, hz, G, mul_comm]
    _ = (∫⁻ z, C.indicator G z ∂(P.prod (expMeasure p))) := by
      simpa only [E, C, G] using hMain
    _ = (∫⁻ z, C.indicator R z * M z ∂(P.prod (expMeasure p))) := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ C <;> simp [Set.indicator, hz, G, mul_comm]
