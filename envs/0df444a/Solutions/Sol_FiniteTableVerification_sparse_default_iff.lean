-- Prove2me | solution 1 for FiniteTableVerification.sparse_default_iff
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T20:46:48.879662+00:00
-- url     : https://prove2.me/submissions/20cd1e76-78c8-4686-bb24-5315f444e0ce

import Mathlib

theorem solution {Key Group Action : Type*}
    [DecidableEq Key] (groupOf : Key → Group) (admissible : Group → Finset Key)
    (listed : Finset Key) (groups : Finset Group) (action : Key → Action) (fallback : Action)
    (valid : Group → Action → Prop)
    (group_consistent : ∀ g k, k ∈ admissible g → groupOf k = g)
    (unlisted_default : ∀ k, k ∉ listed → action k = fallback)
    (unlisted_groups_valid : ∀ g, g ∉ groups → valid g fallback) :
    (∀ k, k ∈ admissible (groupOf k) → valid (groupOf k) (action k)) ↔
      (∀ k ∈ listed, k ∈ admissible (groupOf k) → valid (groupOf k) (action k)) ∧
      (∀ g ∈ groups, ¬ valid g fallback →
        (admissible g ∩ listed).card = (admissible g).card) := by
  constructor
  · intro allValid
    refine ⟨fun k _ => allValid k, ?_⟩
    intro g _ invalidDefault
    have covers : admissible g ⊆ listed := by
      intro k hk
      have hg := group_consistent g k hk
      by_contra missing
      have good := allValid k (hg.symm ▸ hk)
      rw [hg, unlisted_default k missing] at good
      exact invalidDefault good
    exact congrArg Finset.card (Finset.inter_eq_left.mpr covers)
  · rintro ⟨verifyRows, verifyCounts⟩ k hk
    by_cases found : k ∈ listed
    · exact verifyRows k found hk
    · rw [unlisted_default k found]
      by_cases active : groupOf k ∈ groups
      · by_contra invalidDefault
        have exactCount := verifyCounts (groupOf k) active invalidDefault
        have fullRows := Finset.eq_of_subset_of_card_le
          (Finset.inter_subset_left (s₁ := admissible (groupOf k)) (s₂ := listed)) exactCount.ge
        have existsRow : k ∈ admissible (groupOf k) ∩ listed := fullRows.symm ▸ hk
        exact found (Finset.mem_inter.mp existsRow).2
      · exact unlisted_groups_valid (groupOf k) active

#print axioms solution
