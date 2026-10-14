-- Prove2me | solution 1 for GTWSched.NPC.lemma_1_construction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:07:25.072561+00:00
-- url     : https://prove2.me/submissions/1635bee1-8a07-4f00-8407-809b5915ca6c

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

open ProjSchedTW.Complexity

namespace GTWSched.NPC

open Classical

lemma eoAux_length (ys : List ℕ) : ∀ a, (eoAux a ys).length = 2 * ys.length := by
  induction ys with
  | nil => intro a; simp [eoAux]
  | cons y ys ih => intro a; simp [eoAux, ih]; ring

lemma eoAux_ge (ys : List ℕ) : ∀ a, ∀ v ∈ eoAux a ys, a ≤ v := by
  induction ys with
  | nil => intro a v hv; simp [eoAux] at hv
  | cons y ys ih =>
    intro a v hv
    simp only [eoAux, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact le_rfl
    · omega
    · have := ih (a+y+1) v hv; omega

lemma eoAux_pairwise (ys : List ℕ) (hy : ∀ v ∈ ys, 1 < v) :
    ∀ a, (eoAux a ys).Pairwise (· < ·) := by
  induction ys with
  | nil => intro a; simp [eoAux]
  | cons y ys ih =>
    intro a
    have hy0 : 1 < y := hy y (by simp)
    have hrest := ih (fun v hv => hy v (by simp [hv])) (a+y+1)
    simp only [eoAux]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hrest)
    · intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · omega
      · have := eoAux_ge ys (a+y+1) b hb; omega
    · intro b hb
      have := eoAux_ge ys (a+y+1) b hb; omega

lemma eoAux_getD (ys : List ℕ) : ∀ (a i : ℕ), i < ys.length →
    (eoAux a ys).getD (2*i) 0 = a + ∑ j ∈ Finset.range i, (ys.getD j 0 + 1) ∧
    (eoAux a ys).getD (2*i+1) 0 = a + ∑ j ∈ Finset.range i, (ys.getD j 0 + 1) + ys.getD i 0 := by
  induction ys with
  | nil => intro a i hi; simp at hi
  | cons y ys ih =>
    intro a i hi
    cases i with
    | zero => simp [eoAux]
    | succ i =>
      have hi' : i < ys.length := by simpa using hi
      obtain ⟨h1, h2⟩ := ih (a+y+1) i hi'
      rw [Finset.sum_range_succ']
      constructor
      · have : (eoAux a (y :: ys)).getD (2*(i+1)) 0 = (eoAux (a+y+1) ys).getD (2*i) 0 := by
          simp [eoAux, show 2*(i+1) = 2*i+1+1 by ring]
        rw [this, h1]; simp; omega
      · have : (eoAux a (y :: ys)).getD (2*(i+1)+1) 0 = (eoAux (a+y+1) ys).getD (2*i+1) 0 := by
          simp [eoAux, show 2*(i+1)+1 = 2*i+1+1+1 by ring]
        rw [this, h2]; simp; omega

lemma sum_fin_pred (l : List ℕ) (A : Finset (Fin l.length)) :
    ∑ i ∈ A, l.get i = ∑ p ∈ Finset.range l.length,
      if (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) then l.getD p 0 else 0 := by
  rw [Finset.sum_range (fun p => if (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) then l.getD p 0 else 0)]
  have key : ∀ i : Fin l.length, (if (∃ h : i.val < l.length, (⟨i.val, h⟩ : Fin l.length) ∈ A) then l.getD i.val 0 else 0)
      = if i ∈ A then l.get i else 0 := by
    intro i
    have e1 : (∃ h : i.val < l.length, (⟨i.val, h⟩ : Fin l.length) ∈ A) ↔ i ∈ A := by
      constructor
      · rintro ⟨h, hh⟩; exact hh
      · intro h; exact ⟨i.isLt, h⟩
    have e2 : l.getD i.val 0 = l.get i := by simp [List.getD_eq_getElem?_getD]
    by_cases hi : i ∈ A
    · rw [if_pos (e1.mpr hi), if_pos hi, e2]
    · rw [if_neg (fun h => hi (e1.mp h)), if_neg hi]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [Finset.sum_ite_mem]
  simp

lemma sum_range_pairs (h : ℕ → ℕ) (n : ℕ) :
    ∑ p ∈ Finset.range (2*n), h p = ∑ i ∈ Finset.range n, (h (2*i) + h (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring


lemma sum_cancel (L R g h : ℕ → ℕ) (n : ℕ)
    (term : ∀ i ∈ Finset.range n, L i + g i = R i + h i) :
    (∑ i ∈ Finset.range n, L i = ∑ i ∈ Finset.range n, R i) ↔
      (∑ i ∈ Finset.range n, h i = ∑ i ∈ Finset.range n, g i) := by
  have e1 := Finset.sum_congr rfl term
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at e1
  constructor <;> intro h <;> omega

lemma core_alg (x : List ℕ) (n : ℕ) (hlen : x.length = 2*n) (yv : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ i < n, Q (2*i) ↔ ¬ Q (2*i+1))
    (hxo : ∀ i < n, x.getD (2*i+1) 0 = x.getD (2*i) 0 + yv i) :
    (∑ p ∈ Finset.range x.length, (if Q p then x.getD p 0 else 0) =
      ∑ p ∈ Finset.range x.length, (if ¬ Q p then x.getD p 0 else 0)) ↔
    (∑ i ∈ Finset.range n, (if Q (2*i+1) then yv i else 0) =
      ∑ i ∈ Finset.range n, (if ¬ Q (2*i+1) then yv i else 0)) := by
  rw [hlen, sum_range_pairs (fun p => if Q p then x.getD p 0 else 0),
    sum_range_pairs (fun p => if ¬ Q p then x.getD p 0 else 0)]
  have term : ∀ i ∈ Finset.range n,
      ((if Q (2*i) then x.getD (2*i) 0 else 0) + (if Q (2*i+1) then x.getD (2*i+1) 0 else 0))
        + (if ¬ Q (2*i+1) then yv i else 0)
      = ((if ¬ Q (2*i) then x.getD (2*i) 0 else 0) + (if ¬ Q (2*i+1) then x.getD (2*i+1) 0 else 0))
        + (if Q (2*i+1) then yv i else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h1 := hxo i hi'
    have h2 := hQ i hi'
    by_cases h : Q (2*i+1)
    · have h3 : ¬ Q (2*i) := fun h4 => (h2.mp h4) h
      simp only [h, h3, not_true_eq_false, not_false_eq_true, if_true, if_false]
      omega
    · have h3 : Q (2*i) := h2.mpr h
      simp only [h, h3, not_true_eq_false, not_false_eq_true, if_true, if_false]
      omega
  exact sum_cancel _ _ _ _ n term


lemma eoyes_iff (y : List ℕ) :
    EOYes (eoOfPartition y) ↔ ∃ g : ℕ → Prop,
      ∑ i ∈ Finset.range y.length, (if g i then y.getD i 0 else 0) =
      ∑ i ∈ Finset.range y.length, (if ¬ g i then y.getD i 0 else 0) := by
  unfold eoOfPartition
  set x := eoAux 1 y with hx
  have hlen : x.length = 2 * y.length := eoAux_length y 1
  have hxo : ∀ i < y.length, x.getD (2*i+1) 0 = x.getD (2*i) 0 + y.getD i 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := eoAux_getD y 1 i hi
    rw [hx, h1, h2]
  constructor
  · rintro ⟨X1, hpair, hsum⟩
    set Q : ℕ → Prop := fun p => ∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1 with hQdef
    have hQ : ∀ i < y.length, Q (2*i) ↔ ¬ Q (2*i+1) := by
      intro i hi
      have h1 : 2*i < x.length := by omega
      have h2 : 2*i+1 < x.length := by omega
      have := hpair ⟨2*i, h1⟩ ⟨2*i+1, h2⟩ (by simp [Fin.ext_iff]) (by simp; omega)
      constructor
      · rintro ⟨h, hh⟩ ⟨h', hh'⟩
        exact (this.mp hh) hh'
      · intro hn
        have hn' : (⟨2*i+1, h2⟩ : Fin x.length) ∉ X1 := fun hh => hn ⟨h2, hh⟩
        exact ⟨h1, this.mpr hn'⟩
    refine ⟨fun i => Q (2*i+1), ?_⟩
    have e1 := sum_fin_pred x X1
    have e2 := sum_fin_pred x X1ᶜ
    have e3 : ∑ p ∈ Finset.range x.length, (if (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1ᶜ)
        then x.getD p 0 else 0) = ∑ p ∈ Finset.range x.length, (if ¬ Q p then x.getD p 0 else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_range.mp hp
      have : (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1ᶜ) ↔ ¬ Q p := by
        constructor
        · rintro ⟨h, hh⟩ ⟨h', hh'⟩
          exact (Finset.mem_compl.mp hh) hh'
        · intro hn
          refine ⟨hp', ?_⟩
          rw [Finset.mem_compl]
          intro hc; exact hn ⟨hp', hc⟩
      exact if_congr this rfl rfl
    have e4 : ∑ p ∈ Finset.range x.length, (if (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1)
          then x.getD p 0 else 0) = ∑ p ∈ Finset.range x.length, (if Q p then x.getD p 0 else 0) :=
      Finset.sum_congr rfl (fun p _ => if_congr Iff.rfl rfl rfl)
    rw [e1, e2, e3, e4] at hsum
    have this := (core_alg x y.length hlen (fun i => y.getD i 0) Q hQ hxo).mp hsum
    convert this using 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> congr
  · rintro ⟨g, hg⟩
    set P : ℕ → Prop := fun p => if p % 2 = 1 then g (p / 2) else ¬ g (p / 2) with hP
    set X1 : Finset (Fin x.length) := Finset.univ.filter (fun p => P p.val) with hX1
    refine ⟨X1, ?_, ?_⟩
    · intro p q hpq hdiv
      have hmod : p.val % 2 ≠ q.val % 2 := by
        intro h; apply hpq; apply Fin.ext; omega
      simp only [hX1, Finset.mem_filter, Finset.mem_univ, true_and, hP]
      by_cases hp : p.val % 2 = 1
      · have hq : q.val % 2 ≠ 1 := by omega
        simp [hp, hq, hdiv]
      · have hq : q.val % 2 = 1 := by omega
        simp [hp, hq, hdiv]
    · set Q : ℕ → Prop := fun p => p < x.length ∧ P p with hQdef
      have e1 := sum_fin_pred x X1
      have e2 := sum_fin_pred x X1ᶜ
      have eQ : ∀ p, (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1) ↔ Q p := by
        intro p
        constructor
        · rintro ⟨h, hh⟩
          exact ⟨h, by simpa [hX1] using hh⟩
        · rintro ⟨h, hh⟩
          exact ⟨h, by simpa [hX1] using hh⟩
      have e3 : ∑ p ∈ Finset.range x.length, (if (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1ᶜ)
          then x.getD p 0 else 0) = ∑ p ∈ Finset.range x.length, (if ¬ Q p then x.getD p 0 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := Finset.mem_range.mp hp
        have : (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1ᶜ) ↔ ¬ Q p := by
          constructor
          · rintro ⟨h, hh⟩ hc
            exact (Finset.mem_compl.mp hh) ((eQ p).mpr hc |>.choose_spec)
          · intro hn
            refine ⟨hp', ?_⟩
            rw [Finset.mem_compl]
            intro hc; exact hn ((eQ p).mp ⟨hp', hc⟩)
        exact if_congr this rfl rfl
      have e4 : ∑ p ∈ Finset.range x.length, (if (∃ h : p < x.length, (⟨p, h⟩ : Fin x.length) ∈ X1)
          then x.getD p 0 else 0) = ∑ p ∈ Finset.range x.length, (if Q p then x.getD p 0 else 0) :=
        Finset.sum_congr rfl (fun p _ => if_congr (eQ p) rfl rfl)
      rw [e1, e2, e3, e4]
      have hQ : ∀ i < y.length, Q (2*i) ↔ ¬ Q (2*i+1) := by
        intro i hi
        simp only [hQdef, hP]
        have h1 : 2*i < x.length := by omega
        have h2 : 2*i+1 < x.length := by omega
        simp [h1, h2, show (2*i) % 2 ≠ 1 by omega, show (2*i+1) % 2 = 1 by omega,
          show (2*i)/2 = i by omega, show (2*i+1)/2 = i by omega]
      refine (core_alg x y.length hlen (fun i => y.getD i 0) Q hQ hxo).mpr ?_
      have hQg : ∀ i < y.length, Q (2*i+1) ↔ g i := by
        intro i hi
        simp only [hQdef, hP]
        have h2 : 2*i+1 < x.length := by omega
        simp [h2, show (2*i+1) % 2 = 1 by omega, show (2*i+1)/2 = i by omega]
      have s1 : ∑ i ∈ Finset.range y.length, (if Q (2*i+1) then y.getD i 0 else 0) =
          ∑ i ∈ Finset.range y.length, (if g i then y.getD i 0 else 0) :=
        Finset.sum_congr rfl (fun i hi => if_congr (hQg i (Finset.mem_range.mp hi)) rfl rfl)
      have s2 : ∑ i ∈ Finset.range y.length, (if ¬ Q (2*i+1) then y.getD i 0 else 0) =
          ∑ i ∈ Finset.range y.length, (if ¬ g i then y.getD i 0 else 0) :=
        Finset.sum_congr rfl (fun i hi => if_congr (not_congr (hQg i (Finset.mem_range.mp hi))) rfl rfl)
      rw [s1, s2]; exact hg


lemma pred_sum_iff (l : List ℕ) (g : ℕ → Prop) (A : Finset (Fin l.length))
    (hA : ∀ p (h : p < l.length), (⟨p, h⟩ : Fin l.length) ∈ A ↔ g p) :
    ∑ i ∈ A, l.get i = ∑ p ∈ Finset.range l.length, (if g p then l.getD p 0 else 0) ∧
    ∑ i ∈ Aᶜ, l.get i = ∑ p ∈ Finset.range l.length, (if ¬ g p then l.getD p 0 else 0) := by
  constructor
  · rw [sum_fin_pred]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_range.mp hp
    have : (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ A) ↔ g p :=
      ⟨fun ⟨h, hh⟩ => (hA p h).mp hh, fun hg => ⟨hp', (hA p hp').mpr hg⟩⟩
    by_cases hg : g p
    · rw [if_pos (this.mpr hg), if_pos hg]
    · rw [if_neg (fun h => hg (this.mp h)), if_neg hg]
  · rw [sum_fin_pred]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_range.mp hp
    have : (∃ h : p < l.length, (⟨p, h⟩ : Fin l.length) ∈ Aᶜ) ↔ ¬ g p := by
      constructor
      · rintro ⟨h, hh⟩ hg
        exact (Finset.mem_compl.mp hh) ((hA p h).mpr hg)
      · intro hg
        exact ⟨hp', Finset.mem_compl.mpr (fun hh => hg ((hA p hp').mp hh))⟩
    by_cases hg : g p
    · rw [if_neg (fun h => (this.mp h) hg), if_neg (not_not.mpr hg)]
    · rw [if_pos (this.mpr hg), if_pos hg]

lemma partition_iff (y : List ℕ) :
    PartitionYes y ↔ ∃ g : ℕ → Prop,
      ∑ i ∈ Finset.range y.length, (if g i then y.getD i 0 else 0) =
      ∑ i ∈ Finset.range y.length, (if ¬ g i then y.getD i 0 else 0) := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨fun p => ∃ h : p < y.length, (⟨p, h⟩ : Fin y.length) ∈ A, ?_⟩
    have := pred_sum_iff y (fun p => ∃ h : p < y.length, (⟨p, h⟩ : Fin y.length) ∈ A) A
      (fun p h => ⟨fun hh => ⟨h, hh⟩, fun ⟨h', hh⟩ => hh⟩)
    rw [← this.1, ← this.2]; exact hA
  · rintro ⟨g, hg⟩
    refine ⟨Finset.univ.filter (fun i : Fin y.length => g i.val), ?_⟩
    have := pred_sum_iff y g (Finset.univ.filter (fun i : Fin y.length => g i.val))
      (fun p h => by simp)
    rw [this.1, this.2]; exact hg

theorem lemma_1_core (y : List ℕ) (hy : y ≠ []) (hy1 : ∀ v ∈ y, 1 < v) :
    EOInstance (eoOfPartition y) ∧ (PartitionYes y ↔ EOYes (eoOfPartition y)) := by
  refine ⟨?_, (partition_iff y).trans (eoyes_iff y).symm⟩
  unfold EOInstance eoOfPartition
  refine ⟨?_, ?_, ?_, eoAux_pairwise y hy1 1⟩
  · rw [eoAux_length]; exact ⟨y.length, by ring⟩
  · rw [eoAux_length]
    have := List.length_pos_of_ne_nil hy
    omega
  · intro v hv
    have := eoAux_ge y 1 v hv
    omega

end GTWSched.NPC

open GTWSched.NPC


theorem solution (y : List ℕ) (hy : y ≠ []) (hy1 : ∀ v ∈ y, 1 < v) :
    EOInstance (eoOfPartition y) ∧ (PartitionYes y ↔ EOYes (eoOfPartition y)) := by
  exact lemma_1_core y hy hy1
