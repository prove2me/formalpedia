-- Prove2me | solution 1 for FeasibleBasesHC.Structure.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:13:40.972666+00:00
-- url     : https://prove2.me/submissions/aa7c5c20-84a8-4268-b54a-b20978c32472

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

open FeasibleBasesHC.Structure

namespace HCProp2Aux

/-- side of a split vertex: `v_i ↦ 0`, `w_i ↦ 1`. -/
def side {n : ℕ} : GpVertex n → ℤ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

lemma next_bij (L : ℕ) (hL : 0 < L) :
    Function.Bijective (fun i : Fin L => (⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩ : Fin L)) := by
  apply Function.Injective.bijective_of_finite
  intro a b h
  simp only [Fin.mk.injEq] at h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  by_cases h1 : a.val + 1 < L <;> by_cases h2 : b.val + 1 < L
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, show b.val + 1 = L by omega, Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt h2, show a.val + 1 = L by omega, Nat.mod_self] at h; omega
  · omega

end HCProp2Aux

open HCProp2Aux in
theorem solution {n : ℕ} [NeZero n] (G : Digraph n)
    (beta : ℝ) (hpos : 0 < beta) (hlt : beta < 1)
    (C : (Gp G beta).Cycle) :
    C.multiplier = 1 ↔ C.Balanced := by
  classical
  have hL : 0 < C.length := C.length_pos
  let nxt : Fin C.length → Fin C.length := fun i => ⟨(i.val + 1) % C.length, Nat.mod_lt _ hL⟩
  let F : Fin C.length → Prop := fun i => C.forward i = true
  let I : Fin C.length → Prop := fun i => (C.edge i).isLeft = true
  -- indicator counts
  let A : ℤ := ∑ i, if F i ∧ I i then 1 else 0
  let B : ℤ := ∑ i, if F i ∧ ¬ I i then 1 else 0
  let Cc : ℤ := ∑ i, if ¬ F i ∧ I i then 1 else 0
  let D : ℤ := ∑ i, if ¬ F i ∧ ¬ I i then 1 else 0
  -- telescoping identity
  have hstep : ∀ i, side (C.vertex (nxt i)) - side (C.vertex i) =
      (if F i ∧ I i then -1 else 0) + (if F i ∧ ¬ I i then 1 else 0) +
      (if ¬ F i ∧ I i then 1 else 0) + (if ¬ F i ∧ ¬ I i then -1 else 0) := by
    intro i
    have h := C.endpoints i
    simp only at h
    simp only [F, I]
    obtain ⟨e, he⟩ | ⟨e, he⟩ : (∃ e, C.edge i = Sum.inl e) ∨ ∃ e, C.edge i = Sum.inr e := by
      rcases C.edge i with e | e
      · exact Or.inl ⟨e, rfl⟩
      · exact Or.inr ⟨e, rfl⟩
    all_goals
      rw [he] at h
      by_cases hf : C.forward i = true
      · simp only [hf, if_true] at h
        obtain ⟨h1, h2⟩ := h
        simp only [nxt, hf, he, ← h1, ← h2, Gp, side, Sum.isLeft_inl, Sum.isLeft_inr]
        norm_num
      · simp only [hf, Bool.false_eq_true, if_false] at h
        obtain ⟨h1, h2⟩ := h
        simp only [nxt, hf, he, ← h1, ← h2, Gp, side, Sum.isLeft_inl, Sum.isLeft_inr]
        norm_num
  have htel : ∑ i, (side (C.vertex (nxt i)) - side (C.vertex i)) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact Equiv.sum_comp (Equiv.ofBijective nxt (next_bij C.length hL)) (fun j => side (C.vertex j))
  simp only [hstep, Finset.sum_add_distrib] at htel
  have hneg : ∀ (p : Fin C.length → Prop) [DecidablePred p],
      (∑ i, if p i then (-1 : ℤ) else 0) = -∑ i, if p i then (1 : ℤ) else 0 := by
    intro p _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hneg, hneg] at htel
  have hrel : -A + B + Cc - D = 0 := by
    simp only [A, B, Cc, D]; linarith
  -- balanced in terms of counts
  have hcard : ∀ (p : Fin C.length → Prop) [DecidablePred p],
      ((Finset.univ.filter p).card : ℤ) = ∑ i, if p i then (1 : ℤ) else 0 := by
    intro p _
    rw [Finset.card_filter]; push_cast; rfl
  have hsplit : ∀ (p q : Fin C.length → Prop) [DecidablePred p] [DecidablePred q],
      (∑ i, if p i then (1 : ℤ) else 0) =
      (∑ i, if p i ∧ q i then (1 : ℤ) else 0) + (∑ i, if p i ∧ ¬ q i then (1 : ℤ) else 0) := by
    intro p q _ _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p i <;> by_cases hq : q i <;> simp [hp, hq]
  have hbal1 : ((Finset.univ.filter (fun i => C.forward i = true)).card : ℤ) = A + B := by
    rw [hcard, hsplit _ I]
  have hbal2 : ((Finset.univ.filter (fun i => (!C.forward i) = true)).card : ℤ) = Cc + D := by
    rw [hcard, hsplit _ I]
    simp [Cc, D, F]
  have hbal : C.Balanced ↔ A + B = Cc + D := by
    unfold GNF.Cycle.Balanced
    rw [← Nat.cast_inj (R := ℤ), hbal1, hbal2]
  -- multiplier in terms of counts
  have hmu : ∀ i, (if C.forward i then (Gp G beta).mu (C.edge i) else 1) =
      if F i ∧ I i then beta else 1 := by
    intro i
    simp only [F, I]
    obtain ⟨e, he⟩ | ⟨e, he⟩ : (∃ e, C.edge i = Sum.inl e) ∨ ∃ e, C.edge i = Sum.inr e := by
      rcases C.edge i with e | e
      · exact Or.inl ⟨e, rfl⟩
      · exact Or.inr ⟨e, rfl⟩
    all_goals by_cases hf : C.forward i = true <;> simp [hf, he, Gp]
  have hmu' : ∀ i, (if C.forward i then 1 else (Gp G beta).mu (C.edge i)) =
      if ¬ F i ∧ I i then beta else 1 := by
    intro i
    simp only [F, I]
    obtain ⟨e, he⟩ | ⟨e, he⟩ : (∃ e, C.edge i = Sum.inl e) ∨ ∃ e, C.edge i = Sum.inr e := by
      rcases C.edge i with e | e
      · exact Or.inl ⟨e, rfl⟩
      · exact Or.inr ⟨e, rfl⟩
    all_goals by_cases hf : C.forward i = true <;> simp [hf, he, Gp]
  have hprod : ∀ (p : Fin C.length → Prop) [DecidablePred p],
      (∏ i, if p i then beta else 1) = beta ^ (Finset.univ.filter p).card := by
    intro p _
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hmult : C.multiplier = beta ^ (Finset.univ.filter (fun i => F i ∧ I i)).card /
      beta ^ (Finset.univ.filter (fun i => ¬ F i ∧ I i)).card := by
    unfold GNF.Cycle.multiplier
    simp only [hmu, hmu']
    rw [hprod, hprod]
  have hA : (A : ℤ) = ((Finset.univ.filter (fun i => F i ∧ I i)).card : ℤ) := (hcard _).symm
  have hC : (Cc : ℤ) = ((Finset.univ.filter (fun i => ¬ F i ∧ I i)).card : ℤ) := (hcard _).symm
  have hmult1 : C.multiplier = 1 ↔ A = Cc := by
    rw [hmult, hA, hC, Nat.cast_inj]
    have hb0 : beta ^ (Finset.univ.filter (fun i => ¬ F i ∧ I i)).card ≠ 0 :=
      pow_ne_zero _ hpos.ne'
    rw [div_eq_one_iff_eq hb0]
    exact (pow_right_injective₀ hpos hlt.ne).eq_iff
  rw [hmult1, hbal]
  constructor <;> intro h <;> linarith
