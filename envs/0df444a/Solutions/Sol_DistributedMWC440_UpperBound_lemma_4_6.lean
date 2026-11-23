-- Prove2me | solution 1 for DistributedMWC440.UpperBound.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:08.990999+00:00
-- url     : https://prove2.me/submissions/2e38241e-0764-4e5b-a571-b542da74fc1e

import Definitions.Def_DistributedMWC440_UpperBound_Operations
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_index_shifted_exponential_top_gap

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

open StabilityDichotomies.Bijunctive

theorem solution {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (β d : ℝ) (hβ : 0 < β) (hd : 0 ≤ d) :
    ENNReal.ofReal (Real.exp (-β*d)) ≤
      (Measure.pi (fun _ : ι => expMeasure β))
        {δ | ∃ s : ι, ∀ s' : ι, s' ≠ s → a s - δ s < a s' - δ s' - d} := by
  classical
  let μ : Measure (ι → ℝ) := Measure.pi (fun _ : ι => expMeasure β)
  let A : Set (ι → ℝ) :=
    {δ | ∃ s : ι, ∀ s' : ι, s' ≠ s → a s - δ s < a s' - δ s' - d}
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  letI : IsProbabilityMeasure μ := by
    unfold μ
    infer_instance
  have hA : MeasurableSet A := by
    have hAeq : A = ⋃ s : ι, ⋂ s' : ι, ⋂ (_ : s' ≠ s),
        {δ : ι → ℝ | a s - δ s < a s' - δ s' - d} := by
      ext δ
      simp [A]
    rw [hAeq]
    apply MeasurableSet.iUnion
    intro s
    apply MeasurableSet.iInter
    intro s'
    apply MeasurableSet.iInter
    intro hs'
    exact measurableSet_lt
      ((measurable_const : Measurable (fun _ : ι → ℝ => a s)).sub
        (measurable_pi_apply s))
      (((measurable_const : Measurable (fun _ : ι → ℝ => a s')).sub
        (measurable_pi_apply s')).sub_const d)
  change ENNReal.ofReal (Real.exp (-β*d)) ≤ μ A
  by_cases hι : Nontrivial ι
  · letI : Nontrivial ι := hι
    let B : Set (ι → ℝ) :=
      {δ | ∃ i j : ι, i ≠ j ∧
        (∀ k, δ k - a k ≤ δ i - a i) ∧
        (∀ k, k ≠ i → δ k - a k ≤ δ j - a j) ∧
        (δ i - a i) - (δ j - a j) ≤ d}
    have hsub : Aᶜ ⊆ B := by
      intro δ hδ
      have hno : ¬ ∃ s : ι, ∀ s' : ι, s' ≠ s →
          a s - δ s < a s' - δ s' - d := by
        simpa [A] using hδ
      obtain ⟨i, hi⟩ := Finite.exists_max (fun s : ι => δ s - a s)
      obtain ⟨j₀, hj₀⟩ := exists_ne i
      letI : Nonempty {s : ι // s ≠ i} := ⟨⟨j₀, hj₀⟩⟩
      obtain ⟨j, hj⟩ := Finite.exists_max
        (fun s : {s : ι // s ≠ i} => δ s.1 - a s.1)
      change ∃ i j : ι, i ≠ j ∧
        (∀ k, δ k - a k ≤ δ i - a i) ∧
        (∀ k, k ≠ i → δ k - a k ≤ δ j - a j) ∧
        (δ i - a i) - (δ j - a j) ≤ d
      refine ⟨i, j.1, j.property.symm, hi, ?_, ?_⟩
      · intro k hki
        exact hj ⟨k, hki⟩
      · by_contra hngap
        have hgap : d < (δ i - a i) - (δ j.1 - a j.1) := not_le.mp hngap
        apply hno
        refine ⟨i, ?_⟩
        intro s' hs'
        have hs'j := hj ⟨s', hs'⟩
        change a i - δ i < a s' - δ s' - d
        change δ s' - a s' ≤ δ j.1 - a j.1 at hs'j
        nlinarith
    have hcard : 2 ≤ Fintype.card ι := Fintype.one_lt_card
    have hB : (μ B).toReal ≤ 1 - Real.exp (-β*d) := by
      simpa [μ, B] using
        (finite_index_shifted_exponential_top_gap hcard β d hβ hd a)
    have hcoef : 0 ≤ 1 - Real.exp (-β*d) := by
      have he : Real.exp (-β*d) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith
    have hB' : μ B ≤ ENNReal.ofReal (1 - Real.exp (-β*d)) := by
      apply (ENNReal.toReal_le_toReal (measure_ne_top μ B) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal hcoef]
      exact hB
    have hAc : μ Aᶜ ≤ ENNReal.ofReal (1 - Real.exp (-β*d)) :=
      (measure_mono hsub).trans hB'
    have hAformula : μ A = 1 - μ Aᶜ := by
      have hc := measure_compl hA (measure_ne_top μ A)
      rw [measure_univ] at hc
      rw [hc]
      have hAle : μ A ≤ 1 := by
        calc
          μ A ≤ μ Set.univ := measure_mono (Set.subset_univ A)
          _ = 1 := measure_univ
      exact (ENNReal.sub_sub_cancel (by simp) hAle).symm
    rw [hAformula]
    have hexp : Real.exp (-β*d) = 1 - (1 - Real.exp (-β*d)) := by ring
    rw [hexp, ENNReal.ofReal_sub 1 hcoef, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hAc 1
  · haveI : Subsingleton ι := not_nontrivial_iff_subsingleton.mp hι
    have hAuniv : A = Set.univ := by
      ext δ
      simp only [A, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      let s : ι := Classical.choice inferInstance
      refine ⟨s, ?_⟩
      intro s' hs'
      exact (hs' (Subsingleton.elim s' s)).elim
    rw [hAuniv, measure_univ]
    have he : Real.exp (-β*d) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    simpa using ENNReal.ofReal_le_ofReal he
