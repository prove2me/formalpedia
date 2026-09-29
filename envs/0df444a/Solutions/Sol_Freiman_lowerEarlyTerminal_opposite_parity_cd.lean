-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_opposite_parity_cd
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:34:19.881041+00:00
-- url     : https://prove2.me/submissions/b43c800f-4b19-4efa-b90a-e4ce07c0a7e5

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

open Freiman

/-- The fold preserves `1 ≤ c < d`. -/
private theorem inv_step : ∀ (w : List ℕ+) (z : ℕ × ℕ), 1 ≤ z.1 → z.1 < z.2 →
    1 ≤ (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).1 ∧
      (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).1
        < (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).2 := by
  intro w
  induction w with
  | nil => intro z h1 h2; exact ⟨h1, h2⟩
  | cons a t ih =>
    intro z h1 h2
    have ha : 1 ≤ (a : ℕ) := a.property
    have key : z.2 ≤ (a:ℕ) * z.2 := by
      calc z.2 = 1 * z.2 := by ring
        _ ≤ (a:ℕ) * z.2 := Nat.mul_le_mul_right _ ha
    refine ih _ ?_ ?_ <;> simp only <;> omega

/-- For a word whose first letter is at least two, the continuant pair is strictly
ordered; the empty word gives `(0,1)`, which is also strictly ordered. -/
private theorem cd_lt (w : List ℕ+) (h : ∀ a ∈ w.head?, 2 ≤ (a : ℕ)) :
    (lowerCD w).1 < (lowerCD w).2 := by
  cases w with
  | nil => unfold lowerCD; norm_num
  | cons a t =>
    have ha : 2 ≤ (a : ℕ) := h a (by simp)
    have : lowerCD (a :: t) = t.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (1, (a:ℕ)) := by
      unfold lowerCD; simp
    rw [this]
    exact (inv_step t (1,(a:ℕ)) (by norm_num) (by omega)).2

private theorem cd_concat (u : List ℕ+) (a : ℕ+) :
    lowerCD (u ++ [a]) = ((lowerCD u).2, (lowerCD u).1 + (a:ℕ) * (lowerCD u).2) := by
  simp [lowerCD, List.foldl_append]

private theorem head_of_concat {u : List ℕ+} {a : ℕ+}
    (h : ∀ x ∈ (u ++ [a]).head?, 2 ≤ (x : ℕ)) : ∀ x ∈ u.head?, 2 ≤ (x : ℕ) := by
  intro x hx
  apply h
  cases u with
  | nil => simp at hx
  | cons c t => simp_all

private theorem cd_snd_pos (w : List ℕ+) (h : ∀ x ∈ w.head?, 2 ≤ (x : ℕ)) :
    1 ≤ (lowerCD w).2 := by
  have := cd_lt w h; omega

/-- Continuant pairs determine the word, among words whose first letter is at
least two: the Euclidean step recovers the last letter and the previous pair. -/
private theorem cd_inj : ∀ n : ℕ, ∀ u v : List ℕ+, u.length = n →
    (∀ x ∈ u.head?, 2 ≤ (x : ℕ)) → (∀ x ∈ v.head?, 2 ≤ (x : ℕ)) →
    lowerCD u = lowerCD v → u = v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v hlen hu hv heq
    rcases List.eq_nil_or_concat u with rfl | ⟨u', a, rfl⟩
    · rcases List.eq_nil_or_concat v with rfl | ⟨v', b, rfl⟩
      · rfl
      · exfalso
        simp only [List.concat_eq_append] at heq hv
        rw [cd_concat] at heq
        have h1 : (lowerCD ([] : List ℕ+)).1 = 0 := by unfold lowerCD; norm_num
        have h2 := cd_snd_pos v' (head_of_concat hv)
        have := congrArg Prod.fst heq
        rw [h1] at this
        omega
    · rcases List.eq_nil_or_concat v with rfl | ⟨v', b, rfl⟩
      · exfalso
        simp only [List.concat_eq_append] at heq hu
        rw [cd_concat] at heq
        have h1 : (lowerCD ([] : List ℕ+)).1 = 0 := by unfold lowerCD; norm_num
        have h2 := cd_snd_pos u' (head_of_concat hu)
        have := congrArg Prod.fst heq
        rw [h1] at this
        omega
      · simp only [List.concat_eq_append] at heq hu hv hlen ⊢
        have hu' := head_of_concat hu
        have hv' := head_of_concat hv
        rw [cd_concat, cd_concat] at heq
        have hA : (lowerCD u').2 = (lowerCD v').2 := congrArg Prod.fst heq
        have hB : (lowerCD u').1 + (a:ℕ) * (lowerCD u').2
            = (lowerCD v').1 + (b:ℕ) * (lowerCD v').2 := congrArg Prod.snd heq
        have hcu := cd_lt u' hu'
        have hcv := cd_lt v' hv'
        rw [← hA] at hB hcv
        -- the letter is forced
        have hab : (a:ℕ) = (b:ℕ) := by
          by_contra hne
          have hBz : ((lowerCD u').1 : ℤ) + ((a:ℕ):ℤ) * ((lowerCD u').2 : ℤ)
              = ((lowerCD v').1 : ℤ) + ((b:ℕ):ℤ) * ((lowerCD u').2 : ℤ) := by exact_mod_cast hB
          have h1 : ((lowerCD u').1 : ℤ) < ((lowerCD u').2 : ℤ) := by exact_mod_cast hcu
          have h2 : ((lowerCD v').1 : ℤ) < ((lowerCD u').2 : ℤ) := by exact_mod_cast hcv
          rcases Nat.lt_or_ge (a:ℕ) (b:ℕ) with hlt | hge
          · have : ((a:ℕ):ℤ) + 1 ≤ ((b:ℕ):ℤ) := by exact_mod_cast hlt
            nlinarith
          · have : ((b:ℕ):ℤ) + 1 ≤ ((a:ℕ):ℤ) := by
              have : (b:ℕ) < (a:ℕ) := by omega
              exact_mod_cast this
            nlinarith
        have hC : (lowerCD u').1 = (lowerCD v').1 := by
          rw [hab] at hB; omega
        have hcd : lowerCD u' = lowerCD v' := Prod.ext hC hA
        have hlt : u'.length < n := by
          rw [← hlen]; simp
        have := ih u'.length hlt u' v' rfl hu' hv' hcd
        rw [this, PNat.coe_injective hab]

theorem solution (u v : List ℕ+)
    (hu : ∃ a : ℕ+, ∃ w : List ℕ+, u = a::w ∧ 3 ≤ (a:ℕ))
    (hv : ∃ a : ℕ+, ∃ w : List ℕ+, v = a::w ∧ 3 ≤ (a:ℕ))
    (hp : u.length % 2 ≠ v.length % 2) : lowerCD u ≠ lowerCD v := by
  intro heq
  obtain ⟨a, w, rfl, ha⟩ := hu
  obtain ⟨b, z, rfl, hb⟩ := hv
  have hhu : ∀ x ∈ (a :: w).head?, 2 ≤ (x : ℕ) := by
    intro x hx
    simp only [List.head?_cons, Option.mem_some_iff] at hx
    subst hx; omega
  have hhv : ∀ x ∈ (b :: z).head?, 2 ≤ (x : ℕ) := by
    intro x hx
    simp only [List.head?_cons, Option.mem_some_iff] at hx
    subst hx; omega
  have := cd_inj (a :: w).length (a :: w) (b :: z) rfl hhu hhv heq
  rw [this] at hp
  exact hp rfl
