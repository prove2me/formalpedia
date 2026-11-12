-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_count_time_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:19:01.70757+00:00
-- url     : https://prove2.me/submissions/0be3fc9e-b203-4c2b-bfd7-e8c6a8ad6768

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- The natural infimum is a least element or the zero of an empty set. -/
private theorem a06_original_nat_sInf_eq_iff (s : Set ℕ) (k : ℕ) :
    sInf s = k ↔ (k ∈ s ∧ ∀ j < k, j ∉ s) ∨ (s = ∅ ∧ k = 0) := by
  constructor
  · intro h
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact Or.inr ⟨hs, by rw [hs, Nat.sInf_empty] at h; exact h.symm⟩
    · exact Or.inl ⟨h ▸ Nat.sInf_mem hs,
        fun j hj => Nat.notMem_of_lt_sInf (h ▸ hj)⟩
  · rintro (⟨hk, hlt⟩ | ⟨hs, hk⟩)
    · refine le_antisymm (Nat.sInf_le hk) ?_
      by_contra hlt'
      push Not at hlt'
      exact hlt _ hlt' (Nat.sInf_mem ⟨k, hk⟩)
    · rw [hs, hk]
      exact Nat.sInf_empty

/-- Every singleton preimage of the original renewal count is measurable. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (t : ℝ) :
    Measurable (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t) := by
  have hτ := hd.measurable_interarrival
  have harr : ∀ n, Measurable (fun ω => LevyFoundations.arrival τ n ω) :=
    fun n => Finset.measurable_sum _ fun i _ => hτ i
  have hA : ∀ n, MeasurableSet
      {ω : (ℕ → ℝ) × (ℕ → ℝ) | t < LevyFoundations.arrival τ n ω} :=
    fun n => measurableSet_lt measurable_const (harr n)
  refine measurable_to_countable' fun k => ?_
  have hset : (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t) ⁻¹' {k} =
      ({ω : (ℕ → ℝ) × (ℕ → ℝ) | t < LevyFoundations.arrival τ k ω} ∩
        ⋂ j, ⋂ _ : j < k, {ω | ¬ t < LevyFoundations.arrival τ j ω}) ∪
       ((⋂ n, {ω | ¬ t < LevyFoundations.arrival τ n ω}) ∩
        {_ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      LevyFoundations.jumpCount]
    rw [a06_original_nat_sInf_eq_iff]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem]
  rw [hset]
  refine ((hA k).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (hA j).compl)).union
        ((MeasurableSet.iInter fun n => (hA n).compl).inter ?_)
  exact MeasurableSet.const _
