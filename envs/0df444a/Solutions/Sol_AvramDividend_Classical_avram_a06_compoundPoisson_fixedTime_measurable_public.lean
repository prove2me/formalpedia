-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compoundPoisson_fixedTime_measurable_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:58:52.30439+00:00
-- url     : https://prove2.me/submissions/6c6943ec-593e-4695-bb1c-d0f206e590e1

import Mathlib
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_compoundPoisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter
open scoped NNReal ENNReal
noncomputable section

/-- The original compound-Poisson process is measurable at each fixed time. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (b : ℝ)
    (τ Y : ℕ → Ω → ℝ)
    (hτ : ∀ n, Measurable (τ n))
    (hY : ∀ n, Measurable (Y n)) (t : ℝ) :
    Measurable (LevyFoundations.compoundPoisson b τ Y t) := by
  have harr : ∀ n, Measurable (fun ω => LevyFoundations.arrival τ n ω) :=
    fun n => Finset.measurable_sum _ fun i _ => hτ i
  have hA : ∀ n, MeasurableSet {ω : Ω | t < LevyFoundations.arrival τ n ω} :=
    fun n => measurableSet_lt measurable_const (harr n)
  have hsInf (s : Set ℕ) (k : ℕ) :
      sInf s = k ↔ (k ∈ s ∧ ∀ j < k, j ∉ s) ∨ (s = ∅ ∧ k = 0) := by
    constructor
    · intro h
      rcases s.eq_empty_or_nonempty with he | hne
      · exact Or.inr ⟨he, by rw [he, Nat.sInf_empty] at h; exact h.symm⟩
      · exact Or.inl ⟨h ▸ Nat.sInf_mem hne,
          fun j hj => Nat.notMem_of_lt_sInf (h ▸ hj)⟩
    · rintro (⟨hk, hlt⟩ | ⟨he, hk⟩)
      · refine le_antisymm (Nat.sInf_le hk) ?_
        by_contra hlt'
        push Not at hlt'
        exact hlt _ hlt' (Nat.sInf_mem ⟨k, hk⟩)
      · rw [he, hk]
        exact Nat.sInf_empty
  have hcount : Measurable (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t) := by
    refine measurable_to_countable' fun k => ?_
    have hset :
        (fun ω => LevyFoundations.jumpCount
          (fun n => LevyFoundations.arrival τ n ω) t) ⁻¹' {k}
        = ({ω : Ω | t < LevyFoundations.arrival τ k ω} ∩
          ⋂ j, ⋂ _ : j < k, {ω : Ω | ¬ t < LevyFoundations.arrival τ j ω}) ∪
          ((⋂ n, {ω : Ω | ¬ t < LevyFoundations.arrival τ n ω}) ∩
            {_ω : Ω | k = 0}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, LevyFoundations.jumpCount]
      rw [hsInf]
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem]
    rw [hset]
    refine ((hA k).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hA j).compl)).union
      ((MeasurableSet.iInter fun n => (hA n).compl).inter ?_)
    exact MeasurableSet.const _
  have hF : Measurable (fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2, Y n p.1) :=
    measurable_from_prod_countable_left fun k =>
      Finset.measurable_sum (Finset.range k) fun n _ => hY n
  have hg : Measurable
      (fun ω => ∑ n ∈ Finset.range
        (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) t),
        Y n ω) :=
    hF.comp (measurable_id.prodMk hcount)
  have hcp : LevyFoundations.compoundPoisson b τ Y t =
      fun ω => 0 + b * t + ∑ n ∈ Finset.range
        (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) t),
        Y n ω := rfl
  rw [hcp]
  exact hg.const_add _