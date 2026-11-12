-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_finite_grid_count_increment_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:44:57.392036+00:00
-- url     : https://prove2.me/submissions/f88b40f6-0efd-485a-940f-243ec4e3f4ef

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

/-- Characterise the least natural witness, including the empty-set case. -/
private theorem a06_nat_sInf_eq_iff (s : Set ℕ) (k : ℕ) :
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

/-- The original count map is measurable at every fixed horizon. -/
private theorem a06_count_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {τ : ℕ → Ω → ℝ} (hτ : ∀ n, Measurable (τ n)) (t : ℝ) :
    Measurable (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t) := by
  have harr : ∀ n, Measurable (fun ω => LevyFoundations.arrival τ n ω) :=
    fun n => Finset.measurable_sum _ fun i _ => hτ i
  have hA : ∀ n, MeasurableSet
      {ω : Ω | t < LevyFoundations.arrival τ n ω} :=
    fun n => measurableSet_lt measurable_const (harr n)
  refine measurable_to_countable' fun k => ?_
  have hset : (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t) ⁻¹' {k} =
      ({ω : Ω | t < LevyFoundations.arrival τ k ω} ∩
        ⋂ j, ⋂ _ : j < k, {ω : Ω | ¬ t < LevyFoundations.arrival τ j ω}) ∪
       ((⋂ n, {ω : Ω | ¬ t < LevyFoundations.arrival τ n ω}) ∩
        {_ω : Ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      LevyFoundations.jumpCount]
    rw [a06_nat_sInf_eq_iff]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem]
  rw [hset]
  refine ((hA k).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (hA j).compl)).union
        ((MeasurableSet.iInter fun n => (hA n).compl).inter ?_)
  exact MeasurableSet.const _

/-- Difference of original deterministic-horizon counts is measurable. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      ∀ i : Fin n, Measurable (fun ω =>
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)) := by
  intro n t ht i
  exact (a06_count_measurable hd.measurable_interarrival
      (t i.succ : ℝ)).sub
    (a06_count_measurable hd.measurable_interarrival
      (t i.castSucc : ℝ))
