-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_Qp_strict_weak_lower_killing_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:32:17.798802+00:00
-- url     : https://prove2.me/submissions/a7fe1780-e19b-4cf2-9324-849adad7de1b

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_real_exp_clock_lower_age_tie_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Strict and weak lower first-passage survival are genuinely equivalent
under the random-terminal Esscher Qp law for all measurable rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ENNReal.ofReal z.2 < twoSidedExitDownTime X lower z.1}).indicator R z ∂Qp) =
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ENNReal.ofReal z.2 ≤ twoSidedExitDownTime X lower z.1}).indicator R z ∂Qp)) := by
  classical
  intro Qp
  let τ : Ω → ℝ≥0∞ := twoSidedExitDownTime X lower
  let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧ ENNReal.ofReal z.2 < τ z.1}
  let F : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧ ENNReal.ofReal z.2 ≤ τ z.1}
  let B : Set (Ω × ℝ) := {z | z.2 = ((τ z.1).toNNReal : ℝ)}
  have hTie : Qp B = 0 := by
    simpa only [Qp, B, τ] using
      (avram_ws01h_actual_Qp_real_exp_clock_lower_age_tie_zero
        X lower θ p hθ hp)
  have hSubset : F \ E ⊆ B := by
    intro z hz
    have hF : z ∈ F := hz.1
    have hNE : z ∉ E := hz.2
    change 0 ≤ z.2 ∧ ENNReal.ofReal z.2 ≤ τ z.1 at hF
    have hNlt : ¬ ENNReal.ofReal z.2 < τ z.1 := by
      intro hlt
      exact hNE ⟨hF.1, hlt⟩
    have heq : ENNReal.ofReal z.2 = τ z.1 :=
      le_antisymm hF.2 (le_of_not_gt hNlt)
    have hAge : Real.toNNReal z.2 = (τ z.1).toNNReal := by
      have h := congrArg ENNReal.toNNReal heq
      simpa only [ENNReal.ofReal, ENNReal.toNNReal_coe] using h
    change z.2 = (((τ z.1).toNNReal : ℝ≥0) : ℝ)
    calc
      z.2 = (Real.toNNReal z.2 : ℝ) :=
        (Real.coe_toNNReal z.2 hF.1).symm
      _ = ((τ z.1).toNNReal : ℝ) :=
        congrArg (fun v : ℝ≥0 => (v : ℝ)) hAge
  have hNull : Qp (F \ E) = 0 := Measure.mono_null hSubset hTie
  have hAE : ∀ᵐ z ∂Qp, z ∉ F \ E := by
    apply (ae_iff).2
    simp only [not_not]
    change Qp (F \ E) = 0
    exact hNull
  apply lintegral_congr_ae
  filter_upwards [hAE] with z hz
  change E.indicator R z = F.indicator R z
  by_cases he : z ∈ E
  · have hf : z ∈ F := by
      rcases he with ⟨ht0, hlt⟩
      exact ⟨ht0, hlt.le⟩
    simp only [Set.indicator_of_mem he, Set.indicator_of_mem hf]
  · have hf : z ∉ F := by
      intro hf
      exact hz ⟨hf, he⟩
    simp only [Set.indicator_of_notMem he, Set.indicator_of_notMem hf]
