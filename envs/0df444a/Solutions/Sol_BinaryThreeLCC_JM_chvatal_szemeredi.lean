-- Prove2me | solution 1 for BinaryThreeLCC.JM.chvatal_szemeredi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:05:37.907246+00:00
-- url     : https://prove2.me/submissions/b110e06c-b025-40a5-8036-3203afbe9dde

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM.T3aux

variable {V : Type}

/-- A closed walk of length `L`, presented as an `L`-periodic sequence. -/
def CW (R : V → V → Prop) (S : Finset V) (L : ℕ) (w : ℕ → V) : Prop :=
  0 < L ∧ (∀ k, w (k + L) = w k) ∧ (∀ k, w k ∈ S) ∧ ∀ k, R (w k) (w (k + 1))

lemma succ_mod_cases (k L : ℕ) (hL : 0 < L) :
    ((k + 1) % L = k % L + 1 ∧ k % L + 1 < L) ∨ ((k + 1) % L = 0 ∧ k % L + 1 = L) := by
  have h1 := Nat.mod_lt k hL
  have h2 : (k + 1) % L = (k % L + 1) % L := by
    conv_lhs => rw [← Nat.mod_add_div k L]
    rw [show k % L + L * (k / L) + 1 = (k % L + 1) + L * (k / L) by ring]
    exact Nat.add_mul_mod_self_left _ _ _
  rcases Nat.lt_or_ge (k % L + 1) L with h | h
  · left; rw [h2, Nat.mod_eq_of_lt h]; exact ⟨rfl, h⟩
  · right
    have : k % L + 1 = L := by omega
    refine ⟨?_, this⟩; rw [h2, this, Nat.mod_self]

lemma cw_of_mod (R : V → V → Prop) (S : Finset V) (L : ℕ) (f : ℕ → V) (hL : 0 < L)
    (hmem : ∀ k < L, f k ∈ S) (harc : ∀ k, k + 1 < L → R (f k) (f (k + 1)))
    (hlast : R (f (L - 1)) (f 0)) : CW R S L (fun k => f (k % L)) := by
  refine ⟨hL, fun k => by simp [Nat.add_mod_right], fun k => hmem _ (Nat.mod_lt _ hL), ?_⟩
  intro k
  rcases succ_mod_cases k L hL with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h1]; exact harc _ h2
  · simp only [h1]
    have : k % L = L - 1 := by omega
    rw [this]; exact hlast

lemma cw_split (R : V → V → Prop) (S : Finset V) (L : ℕ) (w : ℕ → V) (hw : CW R S L w)
    (i p : ℕ) (hp : 0 < p) (heq : w (i + p) = w i) :
    CW R S p (fun k => w (i + k % p)) := by
  obtain ⟨_, _, hmem, harc⟩ := hw
  refine cw_of_mod R S p (fun k => w (i + k)) hp (fun k _ => hmem _) ?_ ?_
  · intro k _
    have := harc (i + k)
    simpa [Nat.add_assoc] using this
  · have := harc (i + (p - 1))
    rw [show i + (p - 1) + 1 = i + p by omega, heq] at this
    show R (w (i + (p - 1))) (w (i + 0))
    rw [add_zero]; exact this

theorem walk_exists [DecidableEq V] : ∀ (n : ℕ) (S : Finset V) (R : V → V → Prop)
    [DecidableRel R] (r : ℕ), S.card = n → 0 < r → S.Nonempty →
    (∀ x ∈ S, r ≤ (S.filter (fun y => R x y)).card) →
    ∃ L w, CW R S L w ∧ L * (r + 1) ≤ 2 * S.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S R _ r hn hr hS hdeg
  classical
  -- a vertex of large in-degree
  obtain ⟨v0, hv0S, hv0⟩ : ∃ v0 ∈ S, r ≤ (S.filter (fun x => R x v0)).card := by
    have hsum : ∑ x ∈ S, (S.filter (fun y => R x y)).card =
        ∑ y ∈ S, (S.filter (fun x => R x y)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have : ∑ _y ∈ S, r ≤ ∑ y ∈ S, (S.filter (fun x => R x y)).card := by
      rw [← hsum]; exact Finset.sum_le_sum hdeg
    exact Finset.exists_le_of_sum_le hS this
  set A := S.filter (fun x => R x v0) with hAdef
  set B := S.filter (fun y => R v0 y) with hBdef
  have hB : r ≤ B.card := hdeg v0 hv0S
  have hBS : B ⊆ S := Finset.filter_subset _ _
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hBcard : B.card ≤ S.card := Finset.card_le_card hBS
  by_cases hloop : R v0 v0
  · refine ⟨1, _, cw_of_mod R S 1 (fun _ => v0) one_pos (fun _ _ => hv0S)
      (fun k hk => by omega) hloop, ?_⟩
    omega
  have hv0B : v0 ∉ B := fun h => hloop (Finset.mem_filter.1 h).2
  have hv0A : v0 ∉ A := fun h => hloop (Finset.mem_filter.1 h).2
  by_cases hdig : ∃ b ∈ B, b ∈ A
  · obtain ⟨b, hbB, hbA⟩ := hdig
    refine ⟨2, _, cw_of_mod R S 2 (fun k => if k = 0 then v0 else b) two_pos ?_ ?_ ?_, ?_⟩
    · intro k _; split_ifs; exacts [hv0S, hBS hbB]
    · intro k hk
      have : k = 0 := by omega
      subst this; simpa using (Finset.mem_filter.1 hbB).2
    · simpa using (Finset.mem_filter.1 hbA).2
    · have : B ⊆ S.erase v0 := fun x hx =>
        Finset.mem_erase.2 ⟨fun h => hv0B (h ▸ hx), hBS hx⟩
      have h2 := Finset.card_le_card this
      rw [Finset.card_erase_of_mem hv0S] at h2
      omega
  push Not at hdig
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]; intro x hxA hxB; exact hdig x hxB hxA
  have hins : (insert v0 (A ∪ B)).card = A.card + B.card + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [hv0A, hv0B]), Finset.card_union_of_disjoint hdisj]
  have hinsS : insert v0 (A ∪ B) ⊆ S :=
    Finset.insert_subset hv0S (Finset.union_subset hAS hBS)
  have hScard : A.card + B.card + 1 ≤ S.card := hins ▸ Finset.card_le_card hinsS
  by_cases htri : ∃ b ∈ B, ∃ a ∈ A, R b a
  · obtain ⟨b, hbB, a, haA, hba⟩ := htri
    refine ⟨3, _, cw_of_mod R S 3 (fun k => if k = 0 then v0 else if k = 1 then b else a)
      (by norm_num) ?_ ?_ ?_, ?_⟩
    · intro k _; split_ifs; exacts [hv0S, hBS hbB, hAS haA]
    · intro k hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simpa using (Finset.mem_filter.1 hbB).2
      · simpa using hba
    · simpa using (Finset.mem_filter.1 haA).2
    · omega
  push Not at htri
  -- general case
  set S' := S \ insert v0 A with hS'def
  have hiS : insert v0 A ⊆ S := Finset.insert_subset hv0S hAS
  have hS'S : S' ⊆ S := Finset.sdiff_subset
  have hcard' : S'.card + r + 1 ≤ S.card := by
    have h1 := Finset.card_sdiff_add_card_eq_card hiS
    rw [Finset.card_insert_of_notMem hv0A, ← hS'def] at h1
    have hA : r ≤ A.card := hv0
    omega
  have hBS' : B ⊆ S' := by
    intro b hb
    refine Finset.mem_sdiff.2 ⟨hBS hb, ?_⟩
    rw [Finset.mem_insert]; rintro (h | h)
    · exact hv0B (h ▸ hb)
    · exact hdig b hb h
  let R' : V → V → Prop := fun x y => R x y ∨ (y ∈ B ∧ ∃ a ∈ A, R x a)
  have hdeg' : ∀ x ∈ S', r ≤ (S'.filter (fun y => R' x y)).card := by
    intro x hx
    have hxS : x ∈ S := hS'S hx
    have hxA : x ∉ insert v0 A := (Finset.mem_sdiff.1 hx).2
    by_cases hxa : ∃ a ∈ A, R x a
    · calc r ≤ B.card := hB
        _ ≤ _ := Finset.card_le_card (fun b hb =>
          Finset.mem_filter.2 ⟨hBS' hb, Or.inr ⟨hb, hxa⟩⟩)
    · calc r ≤ (S.filter (fun y => R x y)).card := hdeg x hxS
        _ ≤ _ := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨hyS, hxy⟩ := Finset.mem_filter.1 hy
          refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hyS, ?_⟩, Or.inl hxy⟩
          rw [Finset.mem_insert]; rintro (h | h)
          · subst h; exact hxA (Finset.mem_insert.2 (Or.inr (Finset.mem_filter.2 ⟨hxS, hxy⟩)))
          · exact hxa ⟨y, h, hxy⟩
  have hS'ne : S'.Nonempty := by
    obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < B.card)
    exact ⟨b, hBS' hb⟩
  obtain ⟨L', w', ⟨hL', hper, hmem, harc⟩, hbound⟩ :=
    ih S'.card (by omega) S' R' r rfl hr hS'ne hdeg'
  by_cases hall : ∀ k, R (w' k) (w' (k + 1))
  · refine ⟨L', w', ⟨hL', hper, fun k => hS'S (hmem k), hall⟩, ?_⟩
    omega
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  have hex : ∃ t, ¬R (w' (i + 1 + t)) (w' (i + 1 + t + 1)) := by
    refine ⟨L' - 1, ?_⟩
    rw [show i + 1 + (L' - 1) = i + L' by omega, hper,
      show i + L' + 1 = (i + 1) + L' by omega, hper]
    exact hi
  set t := Nat.find hex with htdef
  have ht : ¬R (w' (i + 1 + t)) (w' (i + 1 + t + 1)) := Nat.find_spec hex
  have htmin : ∀ s < t, R (w' (i + 1 + s)) (w' (i + 1 + s + 1)) := by
    intro s hs; have := Nat.find_min hex hs; push Not at this; exact this
  have htle : t ≤ L' - 1 := Nat.find_min' hex (by
    rw [show i + 1 + (L' - 1) = i + L' by omega, hper,
      show i + L' + 1 = (i + 1) + L' by omega, hper]
    exact hi)
  have hbB : w' (i + 1) ∈ B := ((harc i).resolve_left hi).1
  obtain ⟨a, haA, hRa⟩ := ((harc (i + 1 + t)).resolve_left ht).2
  refine ⟨t + 3, _, cw_of_mod R S (t + 3)
    (fun k => if k = 0 then v0 else if k ≤ t + 1 then w' (i + k) else a) (by omega) ?_ ?_ ?_, ?_⟩
  · intro k _
    split_ifs
    exacts [hv0S, hS'S (hmem _), hAS haA]
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa using (Finset.mem_filter.1 hbB).2
    · by_cases hkt : k ≤ t
      · have h1 : k ≠ 0 := by omega
        have h2 : k + 1 ≠ 0 := by omega
        simp only [h1, h2, if_false, show k ≤ t + 1 by omega, show k + 1 ≤ t + 1 by omega,
          if_true]
        have := htmin (k - 1) (by omega)
        rw [show i + 1 + (k - 1) = i + k by omega] at this
        simpa [Nat.add_assoc] using this
      · have hk' : k = t + 1 := by omega
        subst hk'
        simp only [show t + 1 ≠ 0 by omega, show t + 1 + 1 ≠ 0 by omega, if_false, le_refl,
          if_true, show ¬ (t + 1 + 1 ≤ t + 1) by omega]
        rw [show i + (t + 1) = i + 1 + t by omega]
        exact hRa
  · simp only [show t + 3 - 1 = t + 2 by omega, show t + 2 ≠ 0 by omega,
      show ¬ (t + 2 ≤ t + 1) by omega, if_false, if_true]
    exact (Finset.mem_filter.1 haA).2
  · calc (t + 3) * (r + 1) ≤ (L' + 2) * (r + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = L' * (r + 1) + 2 * (r + 1) := by ring
      _ ≤ 2 * S.card := by omega

theorem cycle_of_walk [DecidableEq V] (R : V → V → Prop) (S : Finset V) (L0 : ℕ) (w0 : ℕ → V)
    (h : CW R S L0 w0) :
    ∃ L w, CW R S L w ∧ L ≤ L0 ∧ ∀ i j, i < L → j < L → w i = w j → i = j := by
  classical
  have hP : ∃ L, ∃ w, CW R S L w := ⟨L0, w0, h⟩
  obtain ⟨w, hw⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, w, hw, Nat.find_min' hP ⟨w0, h⟩, ?_⟩
  have key : ∀ i j, i < j → j < Nat.find hP → w i = w j → False := by
    intro i j hij hj heq
    have hc := cw_split R S _ w hw i (j - i) (by omega)
      (by rw [show i + (j - i) = j by omega]; exact heq.symm)
    exact Nat.find_min hP (show j - i < Nat.find hP by omega) ⟨_, hc⟩
  intro i j hi hj heq
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hj heq).elim
  · exact hij
  · exact (key j i hij hi heq.symm).elim

end BinaryThreeLCC.JM.T3aux

namespace BinaryThreeLCC.JM

end BinaryThreeLCC.JM

open BinaryThreeLCC.JM BinaryThreeLCC.JM.T3aux

open T3aux in
/-- T3: Chvátal–Szemerédi. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] (S : Finset V) (r : ℕ) (hr : 0 < r)
    (hS : S.Nonempty) (hdeg : ∀ x ∈ S, r ≤ (S.filter (fun y => R x y)).card) :
    ∃ (l : ℕ) (w : Fin l → V), 0 < l ∧ ((l : ℝ) * (r + 1) ≤ 2 * S.card) ∧
      Function.Injective w ∧ (∀ i, w i ∈ S) ∧ ∀ i : Fin l, R (w i) (w (finRotate l i)) := by
  obtain ⟨L0, w0, hw0, hb⟩ := walk_exists S.card S R r rfl hr hS hdeg
  obtain ⟨L, w, hw, hLL, hinj⟩ := cycle_of_walk R S L0 w0 hw0
  obtain ⟨hL, hper, hmem, harc⟩ := hw
  refine ⟨L, fun i => w i.val, hL, ?_, ?_, fun i => hmem _, ?_⟩
  · have : L * (r + 1) ≤ 2 * S.card := le_trans (Nat.mul_le_mul_right _ hLL) hb
    exact_mod_cast this
  · intro i j h; exact Fin.ext (hinj _ _ i.2 j.2 h)
  · intro i
    obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
    simp only
    rw [finRotate_apply, Fin.val_add_one]
    split_ifs with h
    · subst h
      have h1 := harc n
      have h2 := hper 0
      simp only [zero_add] at h2
      rw [h2] at h1
      simpa using h1
    · exact harc _


namespace BinaryThreeLCC.JM

end BinaryThreeLCC.JM
