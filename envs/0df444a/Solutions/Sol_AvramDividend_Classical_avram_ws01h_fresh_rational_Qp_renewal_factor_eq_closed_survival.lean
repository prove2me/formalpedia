-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_fresh_rational_Qp_renewal_factor_eq_closed_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:00:08.796983+00:00
-- url     : https://prove2.me/submissions/8c7bae0e-39e5-4897-b02a-cdf74e5c3f23

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_rational_fresh_survival_eq_closed
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_full_reward_fubini
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_exp_clock_nonnegative_ae
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The fresh full-future measurable rational reward in the true Qp
killed-record factor is the genuine closed-horizon survival CDF. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) (a : ℝ) :
    (∫⁻ r : ℝ, (∫⁻ ω,
       ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal r) ω -
           (Real.toNNReal r : ℝ) * X.ψ θ)) *
       if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
             (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal r →
               0 ≤ a + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω)
       then (1 : ℝ≥0∞) else 0 ∂P) ∂(expMeasure p)) =
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
         s ≤ Real.toNNReal z.2 → 0 ≤ a + X.X s z.1}).indicator
        (fun _ => (1 : ℝ≥0∞)) z
      ∂((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) := by
  classical
  let D : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))
  let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun u f =>
    if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < u →
        0 ≤ a + f ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
    then 1 else 0
  let F : Ω × ℝ → ℝ≥0∞ := fun z =>
    H (Real.toNNReal z.2) (fun s => X.X s z.1)
  let F' : Ω × ℝ → ℝ≥0∞ := fun z => if 0 ≤ z.2 then F z else 0
  have hJoint := chat04_levy_joint_time_state_measurable X
  have hD : Measurable D :=
    chat04_esscher_likelihood_joint_measurable_of_joint_levy_state X θ hJoint
  have hPath : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) := by
    exact measurable_pi_lambda _ (fun t =>
      hJoint.comp (measurable_const.prodMk measurable_id))
  have hClock : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) := by
    fun_prop
  have hPair : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, fun t : ℝ≥0 => X.X t z.1)) :=
    hClock.prodMk (hPath.comp measurable_fst)
  have hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2) :=
    avram_ws01h_rational_age_fullPath_survival_reward_measurable a
  have hF : Measurable F := hH.comp hPair
  have hF' : Measurable F' :=
    hF.ite (measurableSet_le measurable_const measurable_snd) measurable_const
  have hFubini := avram_ws01h_true_Qp_full_reward_fubini
    P p hp D F hD hF
  have hFubini' := avram_ws01h_true_Qp_full_reward_fubini
    P p hp D F' hD hF'
  have hclock := avram_ws01h_true_exp_clock_nonnegative_ae p hp
  have hRHS :
      (∫⁻ r : ℝ, (∫⁻ ω, D (ω, r) * F (ω, r) ∂P)
        ∂expMeasure p) =
      (∫⁻ r : ℝ, (∫⁻ ω, D (ω, r) * F' (ω, r) ∂P)
        ∂expMeasure p) := by
    apply lintegral_congr_ae
    filter_upwards [hclock] with r hr
    apply lintegral_congr
    intro ω
    simp only [F', if_pos hr]
  have hFresh := avram_ws01h_actual_Qp_rational_fresh_survival_eq_closed
    X θ p hθ hp a
  change (∫⁻ r : ℝ, (∫⁻ ω, D (ω, r) * F (ω, r) ∂P)
    ∂expMeasure p) = _
  calc
    _ = (∫⁻ r : ℝ, (∫⁻ ω, D (ω, r) * F' (ω, r) ∂P)
        ∂expMeasure p) := hRHS
    _ = ∫⁻ z : Ω × ℝ, F' z ∂((P.prod (expMeasure p)).withDensity D) :=
      hFubini'.symm
    _ = (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal z.2 →
          0 ≤ a + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1}).indicator
          (fun _ => (1 : ℝ≥0∞)) z
       ∂((P.prod (expMeasure p)).withDensity D)) := by
       apply lintegral_congr
       intro z
       by_cases ht : 0 ≤ z.2
       · simp [F', F, H, Set.indicator, ht]
       · simp [F', F, H, Set.indicator, ht]
    _ = _ := by simpa only [D] using hFresh
