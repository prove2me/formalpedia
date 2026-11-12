-- Prove2me | solution 1 for FoundationsRL.DECExamples.cover_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:21:15.223352+00:00
-- url     : https://prove2.me/submissions/c0dbf32e-912f-4450-8f1c-d352a52e1b73

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_lipschitzClass
open scoped NNReal

open FoundationsRL.DECExamples in
theorem solution {D : Type*} [MetricSpace D] [MeasurableSpace D] [BorelSpace D] (ε : ℝ≥0)
    (D' : Finset D) (hcover : Metric.IsCover ε Set.univ (D' : Set D)) (f : D → ℝ)
    (hf : f ∈ lipschitzClass D) (μ : MeasureTheory.Measure D)
    [MeasureTheory.IsProbabilityMeasure μ] :
    (∃ ι : D → D, ∀ π, ι π ∈ D' ∧ dist π (ι π) ≤ ε) ∧
    (∀ ι : D → D, (∀ π, ι π ∈ D' ∧ dist π (ι π) ≤ ε) → ∀ π₀ : D,
      ∫ π, (f π₀ - f π) ∂μ ≤ ∫ π, (f (ι π₀) - f π) ∂μ + |f π₀ - f (ι π₀)| ∧
      ∫ π, (f (ι π₀) - f π) ∂μ + |f π₀ - f (ι π₀)| ≤
          ∫ π, (f (ι π₀) - f π) ∂μ + dist π₀ (ι π₀) ∧
      ∫ π, (f (ι π₀) - f π) ∂μ + dist π₀ (ι π₀) ≤ ∫ π, (f (ι π₀) - f π) ∂μ + ε) ∧
    ∫ π, ((⨆ π', f π') - f π) ∂μ ≤ ∫ π, ((⨆ π' : D', f π') - f π) ∂μ + ε := by
  obtain ⟨hbd, hlip⟩ := hf
  have hdist : ∀ x y : D, |f x - f y| ≤ dist x y := by
    intro x y
    have := hlip.dist_le_mul x y
    rw [Real.dist_eq] at this
    simpa using this
  have hint : MeasureTheory.Integrable f μ := by
    refine MeasureTheory.Integrable.of_bound hlip.continuous.aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hbd x).1, (hbd x).2]
  have hI : ∀ c : ℝ, ∫ π, (c - f π) ∂μ = c - ∫ π, f π ∂μ := by
    intro c
    rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const c) hint,
      MeasureTheory.integral_const]
    simp
  have hex : ∃ ι : D → D, ∀ π, ι π ∈ D' ∧ dist π (ι π) ≤ ε := by
    have h := fun π : D => hcover (Set.mem_univ π)
    choose ι hι1 hι2 using h
    refine ⟨ι, fun π => ⟨hι1 π, ?_⟩⟩
    have h2 : edist π (ι π) ≤ ε := hι2 π
    have h3 : nndist π (ι π) ≤ ε := edist_le_coe.1 h2
    rw [dist_nndist]
    exact_mod_cast h3
  refine ⟨hex, ?_, ?_⟩
  · intro ι hι π₀
    rw [hI, hI]
    refine ⟨?_, ?_, ?_⟩
    · have := le_abs_self (f π₀ - f (ι π₀))
      linarith
    · linarith [hdist π₀ (ι π₀)]
    · linarith [(hι π₀).2]
  · rw [hI, hI]
    obtain ⟨ι, hι⟩ := hex
    have hsup : (⨆ π', f π') ≤ (⨆ π' : D', f π') + ε := by
      rcases isEmpty_or_nonempty D with hD | hD
      · haveI : IsEmpty D' := ⟨fun x => hD.false x.1⟩
        simp
      · apply ciSup_le
        intro π
        have hb : BddAbove (Set.range (fun π' : D' => f π')) := by
          refine ⟨1, ?_⟩
          rintro _ ⟨x, rfl⟩
          exact (hbd x).2
        have h1 : f (ι π) ≤ ⨆ π' : D', f π' := le_ciSup hb ⟨ι π, (hι π).1⟩
        have h2 := hdist π (ι π)
        have h3 := (hι π).2
        have h4 := le_abs_self (f π - f (ι π))
        linarith
    linarith
