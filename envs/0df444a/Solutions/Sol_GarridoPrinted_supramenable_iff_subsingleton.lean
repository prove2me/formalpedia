-- Prove2me | solution 1 for GarridoPrinted.supramenable_iff_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T21:52:56.801987+00:00
-- url     : https://prove2.me/submissions/d7d50da5-a253-4a69-a004-9ea238e8bd5b

import Definitions.Def_Garrido_Amenability
import Mathlib


section
section
namespace GarridoPrinted

theorem supramenable_iff_subsingleton (G : Type*) [Group G] :
    (∀ A : Set G, A.Nonempty → ∃ m : Set G → ENNReal,
      Garrido.IsFinitelyAdditiveMeasure m ∧ (∀ s, m s ≤ 1) ∧ m A = 1 ∧ Garrido.IsInvariant G m) ↔
      Subsingleton G := by
  constructor
  · intro h
    obtain ⟨m, ⟨-, hadd⟩, hle, h1, hinv⟩ := h {1} (Set.singleton_nonempty 1)
    have key : ∀ g : G, g = 1 := by
      intro g
      by_contra hg
      have hg1 : m {g} = 1 := by
        have := hinv g {1}
        rw [Set.smul_set_singleton, smul_eq_mul, mul_one] at this
        rw [this, h1]
      have h2 := hadd {1} {g} (Set.disjoint_singleton.2 (Ne.symm hg))
      rw [h1, hg1] at h2
      have := hle ({1} ∪ {g})
      rw [h2] at this
      norm_num at this
    exact ⟨fun a b => by rw [key a, key b]⟩
  · classical
    intro hs A hA
    refine ⟨fun s => if s.Nonempty then 1 else 0, ⟨by simp, ?_⟩, ?_, by simp [hA], ?_⟩
    · intro s t hst
      by_cases hs' : s.Nonempty <;> by_cases ht' : t.Nonempty
      · exfalso
        obtain ⟨x, hx⟩ := hs'
        obtain ⟨y, hy⟩ := ht'
        obtain rfl := Subsingleton.elim x y
        exact Set.disjoint_left.1 hst hx hy
      · simp [hs', Set.not_nonempty_iff_eq_empty.1 ht']
      · simp [ht', Set.not_nonempty_iff_eq_empty.1 hs']
      · simp [Set.not_nonempty_iff_eq_empty.1 hs', Set.not_nonempty_iff_eq_empty.1 ht']
    · intro s
      dsimp only
      split_ifs <;> simp
    · intro g s
      simp [Set.smul_set_nonempty]

end GarridoPrinted

end
end

section
open GarridoPrinted

theorem solution (G : Type*) [Group G] :
    (∀ A : Set G, A.Nonempty → ∃ m : Set G → ENNReal,
      Garrido.IsFinitelyAdditiveMeasure m ∧ (∀ s, m s ≤ 1) ∧ m A = 1 ∧ Garrido.IsInvariant G m) ↔
      Subsingleton G := by
  apply GarridoPrinted.supramenable_iff_subsingleton <;> assumption

end
