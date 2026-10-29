-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_true_Qp_terminal_exp_moment_rate_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T21:22:41.97086+00:00
-- url     : https://prove2.me/submissions/5dcb918b-e1a7-4a63-af3b-ff1dd615de1a

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_esscher_fixed_clock_fibre_terminal_mgf
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_scalar_rate_gap_mgf
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (φ q p β : ℝ) (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q) (hp : 0 < p) (hβ : 0 ≤ β) (hgap : X.ψ (φ + β) - q < p) (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) : ENNReal.ofReal (p - (X.ψ (φ + β) - q)) * (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * X.X (Real.toNNReal z.2) z.1)) ∂((P.prod (ProbabilityTheory.expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) = ENNReal.ofReal p := by
  let a : ℝ := X.ψ (φ + β) - q
  have ha : a < p := hgap
  have hpos : 0 < p - a := sub_pos.mpr ha
  have hθ : 0 ≤ φ + β := add_nonneg hφ.le hβ
  let density : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ φ))
  let W : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (β * X.X (Real.toNNReal z.2) z.1))
  have hClock : Measurable (fun z : Ω × ℝ => (Real.toNNReal z.2, z.1)) := (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hXt : Measurable (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) := (chat04_levy_joint_time_state_measurable X).comp hClock
  have hW : Measurable W := ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (measurable_const.mul hXt))
  have hDens : Measurable density := hJoint
  have hProd : Measurable (fun z : Ω × ℝ => density z * W z) := hDens.mul hW
  have hInner (t : ℝ) :
      (∫⁻ ω : Ω, density (ω,t) * W (ω,t) ∂P) =
        ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)) := by
    exact avram_ws01e_b_genuine_esscher_fixed_clock_fibre_terminal_mgf
      X φ q β hroot hθ t
  have hClockMoment : (∫⁻ z : Ω × ℝ, W z ∂((P.prod (expMeasure p)).withDensity density)) = (∫⁻ t : ℝ, exponentialPDF p t * ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)) ∂volume) := by
    calc
      _ = (∫⁻ z : Ω × ℝ, density z * W z ∂(P.prod (expMeasure p))) := by
        rw [lintegral_withDensity_eq_lintegral_mul
          (P.prod (expMeasure p)) hDens hW]
        rfl
      _ = (∫⁻ t : ℝ, exponentialPDF p t *
            (∫⁻ ω : Ω, density (ω,t) * W (ω,t) ∂P) ∂volume) := by
        simpa using
          (chat04_exponential_clock_killed_reward_tonelli P p hp
            (Set.univ : Set (Ω × ℝ)) MeasurableSet.univ
            (fun z : Ω × ℝ => density z * W z) hProd)
      _ = _ := by
        congr 1
        funext t
        rw [hInner t]
  change ENNReal.ofReal (p - a) *
    (∫⁻ z : Ω × ℝ, W z
      ∂((P.prod (expMeasure p)).withDensity density)) = ENNReal.ofReal p
  rw [hClockMoment]
  exact avram_ws01e_b_exp_clock_scalar_rate_gap_mgf p a hp ha
