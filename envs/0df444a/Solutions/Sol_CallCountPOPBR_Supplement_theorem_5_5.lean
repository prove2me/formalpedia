-- Prove2me | solution 1 for CallCountPOPBR.Supplement.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:28:09.012229+00:00
-- url     : https://prove2.me/submissions/8f767dd5-4944-42e4-b334-1abe592ace8d

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_DecSpec_unfold
import Definitions.Def_CallCountPOPBR_Supplement_RecConsistent

set_option autoImplicit false

namespace CC55Aux
open CallCountPOPBR.Supplement

lemma unfold_eq (s : DecSpec) (n : ℕ) : s.unfold n = .node n ((s.calls n).map s.unfold) := by
  rw [DecSpec.unfold]
  congr 1
  conv_rhs => rw [← List.attach_map_subtype_val (s.calls n), List.map_map]
  rfl

lemma label_unfold (s : DecSpec) (n : ℕ) : (s.unfold n).label = n := by
  rw [unfold_eq]; rfl

lemma children_unfold (s : DecSpec) (n : ℕ) : (s.unfold n).children = (s.calls n).map s.unfold := by
  rw [unfold_eq]; rfl

lemma sub_unfold (s : DecSpec) : ∀ t T, LTree.Sub t T → ∀ n, T = s.unfold n → ∃ k, t = s.unfold k := by
  intro t T h
  induction h with
  | refl => intro n hn; exact ⟨n, hn⟩
  | child hu _ ih =>
    intro n hn
    rw [unfold_eq] at hn
    injection hn with hl hts
    rw [hts, List.mem_map] at hu
    obtain ⟨k, _, hk⟩ := hu
    exact ih k hk.symm

end CC55Aux

open CallCountPOPBR.Supplement in
theorem solution (b : ℕ) (T : ℕ → LTree) :
    (∃ s : DecSpec, (∀ n, (s.calls n).length ≤ b) ∧ ∀ n, T n = s.unfold n) ↔
      (RecConsistent T ∧ ∀ n t, LTree.Sub t (T n) → t.children.length ≤ b) := by
  constructor
  · rintro ⟨s, hb, hT⟩
    have hTf : T = s.unfold := funext hT
    subst hTf
    refine ⟨⟨fun n => CC55Aux.label_unfold s n, ?_, ?_⟩, ?_⟩
    · intro n t ht u hu
      obtain ⟨k, rfl⟩ := CC55Aux.sub_unfold s t _ ht n rfl
      rw [CC55Aux.children_unfold, List.mem_map] at hu
      obtain ⟨j, hj, rfl⟩ := hu
      rw [CC55Aux.label_unfold, CC55Aux.label_unfold]
      exact s.dec k j hj
    · intro n t ht
      obtain ⟨k, rfl⟩ := CC55Aux.sub_unfold s t _ ht n rfl
      rw [CC55Aux.label_unfold]
    · intro n t ht
      obtain ⟨k, rfl⟩ := CC55Aux.sub_unfold s t _ ht n rfl
      rw [CC55Aux.children_unfold, List.length_map]
      exact hb k
  · rintro ⟨⟨hlab, hdec, hiso⟩, hb⟩
    have hdec' : ∀ n, ∀ k ∈ (T n).children.map LTree.label, k < n := by
      intro n k hk
      rw [List.mem_map] at hk
      obtain ⟨u, hu, rfl⟩ := hk
      have := hdec n (T n) (LTree.Sub.refl _) u hu
      rwa [hlab] at this
    let s : DecSpec := ⟨fun n => (T n).children.map LTree.label, hdec'⟩
    refine ⟨s, fun n => ?_, fun n => ?_⟩
    · show ((T n).children.map LTree.label).length ≤ b
      rw [List.length_map]; exact hb n (T n) (LTree.Sub.refl _)
    · induction n using Nat.strong_induction_on with
      | _ n ih =>
        rw [CC55Aux.unfold_eq]
        show T n = LTree.node n (((T n).children.map LTree.label).map s.unfold)
        rw [List.map_map]
        have hc : ∀ u ∈ (T n).children, (s.unfold ∘ LTree.label) u = u := by
          intro u hu
          have hsub : LTree.Sub u (T n) := by
            cases hTn : T n with
            | node l ts =>
              rw [hTn] at hu
              exact LTree.Sub.child hu (LTree.Sub.refl u)
          have hlt : u.label < n := by
            have := hdec n (T n) (LTree.Sub.refl _) u hu
            rwa [hlab] at this
          simp only [Function.comp]
          rw [← ih u.label hlt]
          exact (hiso n u hsub).symm
        rw [List.map_congr_left hc, List.map_id']
        have hl := hlab n
        cases hTn : T n with
        | node l ts =>
          rw [hTn] at hl
          simp only [LTree.label] at hl
          subst hl
          rfl
