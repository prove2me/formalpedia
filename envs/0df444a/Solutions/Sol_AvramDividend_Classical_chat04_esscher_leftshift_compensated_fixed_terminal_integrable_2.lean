-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_leftshift_compensated_fixed_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:27:14.497197+00:00
-- url     : https://prove2.me/submissions/a7356fa0-18c2-4671-a77a-d063ddd53fea

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_integrable_iff_of_ambient_measures_agree_on_subsigma
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_exp_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T) :
    Integrable (fun ω : Ω => Real.exp
      (-ε * X.X s ω -
        (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) := by
  let Q : ℝ≥0 → Measure Ω := fun r =>
    P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X r ω - (r : ℝ) * X.ψ θ)))
  let Z : ℝ≥0 → Ω → ℝ := fun r ω =>
    Real.exp (-ε * X.X r ω -
      (r : ℝ) * (X.ψ (θ - ε) - X.ψ θ))
  have hQs : Integrable (Z s) (Q s) := by
    have hraw := chat04_esscher_finite_negative_exp_integrable
      X s θ ε hθ hε hεθ
    have heq : (fun ω : Ω => Z s ω) =
        (fun ω : Ω => Real.exp
          (-(s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) *
          Real.exp (-ε * X.X s ω)) := by
      funext ω
      dsimp [Z]
      rw [← Real.exp_add]
      congr 1
      ring
    change Integrable (fun ω : Ω => Z s ω) (Q s)
    rw [heq]
    exact hraw.const_mul _
  have hQ : ∀ B : Set Ω, @MeasurableSet Ω (𝓕 s) B →
      Q s B = Q T B := by
    intro B hB
    simpa only [Q, SpectrallyNegativeLevy.ψ] using
      chat04_esscher_finite_horizon_laws_consistent_on_past_events
        X θ hθ s T hsT B hB
  have hadapt : StronglyMeasurable[𝓕 s] (Z s) :=
    chat04_esscher_compensated_leftshift_reward_strongly_adapted
      X θ ε s
  have htransfer :=
    (integrable_iff_of_ambient_measures_agree_on_subsigma
      (𝓕.le s) (Q s) (Q T) hQ (Z s) hadapt).mp hQs
  simpa only [Q, Z] using htransfer
