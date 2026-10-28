-- Prove2me | solution 1 for AvramDividend.Classical.exp_clock_random_age_joint_reward_shift_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:12:38.882987+00:00
-- url     : https://prove2.me/submissions/c787c5f9-5116-41d0-a2d8-d4dbe5fcc714

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_clock_residual_density_lintegral_shift_ws01d

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact joint product-clock memorylessness after a measurable random age.
The reward need only be nonnegative and jointly measurable; no stopping-time
or independence assumption beyond the real external exponential clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p)
    (age : Ω → ℝ≥0) (hAge : Measurable age)
    (reward : Ω × ℝ → ℝ≥0∞) (hReward : Measurable reward) :
    (∫⁻ z : Ω × ℝ, if (age z.1 : ℝ) ≤ z.2 then
       reward (z.1, z.2 - (age z.1 : ℝ)) else 0
       ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (-(p * (age ω : ℝ)))) *
      (∫⁻ u : ℝ, reward (ω, u)
        ∂(ProbabilityTheory.expMeasure p)) ∂P) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  let S : Set (Ω × ℝ) :=
    {z | (age z.1 : ℝ) ≤ z.2}
  let G : Ω × ℝ → ℝ≥0∞ := fun z =>
    reward (z.1, z.2 - (age z.1 : ℝ))
  have hAgeReal : Measurable (fun ω : Ω => (age ω : ℝ)) :=
    hAge.coe_nnreal_real
  have hS : MeasurableSet S := by
    exact measurableSet_le
      (hAgeReal.comp measurable_fst) measurable_snd
  have hG : Measurable G := by
    dsimp [G]
    exact hReward.comp (measurable_fst.prodMk
      (measurable_snd.sub (hAgeReal.comp measurable_fst)))
  have hPiece : Measurable (S.indicator G) :=
    hG.indicator hS
  have hPDF : Measurable (ProbabilityTheory.exponentialPDF p) :=
    (ProbabilityTheory.measurable_exponentialPDFReal p).ennreal_ofReal
  have hKernel (ω : Ω) :
      (∫⁻ t : ℝ,
        (S.indicator G) (ω, t)
          ∂(ProbabilityTheory.expMeasure p)) =
      ENNReal.ofReal (Real.exp (-(p * (age ω : ℝ)))) *
        (∫⁻ u : ℝ, reward (ω, u)
          ∂(ProbabilityTheory.expMeasure p)) := by
    have hFω : Measurable (fun u : ℝ => reward (ω, u)) :=
      hReward.comp (measurable_const.prodMk measurable_id)
    have hIω : Measurable (fun t : ℝ =>
        (S.indicator G) (ω, t)) :=
      hPiece.comp (measurable_const.prodMk measurable_id)
    have hPDFmeasure (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
        (∫⁻ t : ℝ, f t
          ∂(ProbabilityTheory.expMeasure p)) =
        (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
          f t ∂volume) := by
      change (∫⁻ t : ℝ, f t
        ∂(volume.withDensity (ProbabilityTheory.exponentialPDF p))) = _
      exact lintegral_withDensity_eq_lintegral_mul volume hPDF hf
    calc
      _ = (∫⁻ t : ℝ,
          ProbabilityTheory.exponentialPDF p t *
          (S.indicator G) (ω, t) ∂volume) :=
        hPDFmeasure _ hIω
      _ = (∫⁻ t : ℝ, if (age ω : ℝ) ≤ t then
          ProbabilityTheory.exponentialPDF p t *
            reward (ω, t - (age ω : ℝ)) else 0 ∂volume) := by
        congr 1
        funext t
        by_cases ht : (age ω : ℝ) ≤ t
        · simp [S, G, ht, Set.indicator]
        · simp [S, G, ht, Set.indicator]
      _ = ENNReal.ofReal (Real.exp (-(p * (age ω : ℝ)))) *
          (∫⁻ t : ℝ,
            ProbabilityTheory.exponentialPDF p t *
              reward (ω, t) ∂volume) :=
        exp_clock_residual_density_lintegral_shift_ws01d
          p hp (age ω) (fun t => reward (ω,t)) hFω
      _ = _ := by rw [← hPDFmeasure _ hFω]
  change (∫⁻ z : Ω × ℝ, S.indicator G z
    ∂(P.prod (ProbabilityTheory.expMeasure p))) = _
  rw [lintegral_prod (S.indicator G) hPiece.aemeasurable]
  congr 1
  funext ω
  exact hKernel ω
