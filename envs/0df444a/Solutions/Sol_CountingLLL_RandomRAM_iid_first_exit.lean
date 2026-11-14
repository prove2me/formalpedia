-- Prove2me | solution 1 for CountingLLL.RandomRAM.iid_first_exit
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:51:18.651552+00:00
-- url     : https://prove2.me/submissions/ea944a6c-e9e0-40aa-8fb0-2435f7672611

import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_expected_cost

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem solution {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (S T : Set β) (hS : MeasurableSet S) (hT : MeasurableSet T) (hst : Disjoint S T) :
    let μ := Measure.infinitePi fun _ : ℕ => ν
    μ {ω : ℕ → β | ∃ n, (∀ i < n, ω i ∈ S) ∧ ω n ∈ T} = ν T / (1 - ν S) := by
  classical
  dsimp only
  let E : Set (ℕ → β) := {ω | ∃ n, (∀ i < n, ω i ∈ S) ∧ ω n ∈ T}
  have hE : MeasurableSet E := by
    have hEq : E = ⋃ n : ℕ, (⋂ i : Fin n, {ω : ℕ → β | ω i.val ∈ S}) ∩ {ω | ω n ∈ T} := by
      ext ω
      simp only [E, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨n, hn, h⟩
        exact ⟨n, fun i => hn i.val i.isLt, h⟩
      · rintro ⟨n, hn, h⟩
        exact ⟨n, fun i hi => hn ⟨i, hi⟩, h⟩
    rw [hEq]
    exact MeasurableSet.iUnion fun n => (MeasurableSet.iInter fun i => hS.preimage (measurable_pi_apply i.val)).inter (hT.preimage (measurable_pi_apply n))
  have hpoint (ω : ℕ → β) : (∑' n : ℕ,
      ({ω' : ℕ → β | ∀ i < n, ω' i ∈ S}).indicator (fun ω => T.indicator (1 : β → ℝ≥0∞) (ω n)) ω) = E.indicator 1 ω := by
    by_cases he : ω ∈ E
    · obtain ⟨n, hn, ht⟩ := he
      have he' : ω ∈ E := ⟨n, hn, ht⟩
      rw [tsum_eq_single n]
      · have hw : ω ∈ {ω' : ℕ → β | ∀ i < n, ω' i ∈ S} := hn
        rw [Set.indicator_of_mem hw, Set.indicator_of_mem ht, Set.indicator_of_mem he']
        rfl
      · intro m hmn
        by_cases hm : ∀ i < m, ω i ∈ S
        · by_cases hmt : ω m ∈ T
          · have : m < n ∨ n < m := lt_or_gt_of_ne hmn
            rcases this with hmn' | hnm
            · exact False.elim ((Set.disjoint_left.mp hst (hn m hmn')) hmt)
            · exact False.elim ((Set.disjoint_left.mp hst (hm n hnm)) ht)
          · simp [hm, hmt]
        · simp [hm]
    · have hzero (n : ℕ) : ({ω' : ℕ → β | ∀ i < n, ω' i ∈ S}).indicator (fun ω => T.indicator (1 : β → ℝ≥0∞) (ω n)) ω = 0 := by
        by_cases hn : ∀ i < n, ω i ∈ S
        · have ht : ω n ∉ T := by intro ht; exact he ⟨n, hn, ht⟩
          simp [hn, ht]
        · simp [hn]
      simp [hzero, he]
  have hc := CountingLLL.RandomRAM.reciprocal_expected_cost ν S hS (T.indicator (1 : β → ℝ≥0∞)) (measurable_one.indicator hT)
  have hi : (∫⁻ ω, ∑' n : ℕ,
      ({ω' : ℕ → β | ∀ i < n, ω' i ∈ S}).indicator (fun ω => T.indicator (1 : β → ℝ≥0∞) (ω n)) ω ∂(Measure.infinitePi fun _ : ℕ => ν)) = (Measure.infinitePi fun _ : ℕ => ν) E := by
    rw [lintegral_congr hpoint, lintegral_indicator_one hE]
  rw [hi, lintegral_indicator_one hT] at hc
  exact hc
