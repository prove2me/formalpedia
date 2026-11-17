-- Prove2me | solution 1 for DirKECC1549.Asm.dstate_push
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:46.289613+00:00
-- url     : https://prove2.me/submissions/1ed52006-2824-439a-916b-16caad762877

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Main.CostAux

open DirKECC1549.Main

/-! ## Exponents -/

/-! ## Powers of `n` -/

/-! ## Combinatorial constants -/

/-! ## Walks and cuts -/

variable {n m : ℕ}

theorem walk_append (D : Fin m → Fin n × Fin n) {a b c : Fin n} {p q : List (Fin m)}
    (hp : IsWalk D a p b) (hq : IsWalk D b q c) : IsWalk D a (p ++ q) c := by
  induction hp with
  | nil => simpa using hq
  | cons e p he _ ih => exact IsWalk.cons e (p ++ q) he (ih hq)

theorem reach_trans (D : Fin m → Fin n × Fin n) {a b c : Fin n} (h1 : Reach D a b)
    (h2 : Reach D b c) : Reach D a c := by
  obtain ⟨p, hp⟩ := h1; obtain ⟨q, hq⟩ := h2; exact ⟨p ++ q, walk_append D hp hq⟩

/-! ## Strongly connected components -/

end DirKECC1549.Main.CostAux
end

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

theorem reach_refl (D : Fin m → Fin n × Fin n) (a : Fin n) : Reach D a a := ⟨[], IsWalk.nil a⟩

theorem reach_edge (D : Fin m → Fin n × Fin n) (e : Fin m) : Reach D (D e).1 (D e).2 :=
  ⟨[e], IsWalk.cons e [] rfl (IsWalk.nil _)⟩

end DirKECC1549.Asm

namespace DirKECC1549.Asm

/-- A down-closed set of positions of size `c` is `{i < c}`. -/
theorem downset_iff {m : ℕ} (S : Finset (Fin m)) (hS : ∀ i j : Fin m, j ≤ i → i ∈ S → j ∈ S)
    (i : Fin m) : i ∈ S ↔ (i : ℕ) < S.card := by
  constructor
  · intro hi
    have : (univ.filter (fun j : Fin m => j ≤ i)) ⊆ S := fun j hj => hS i j (by simpa using hj) hi
    have h2 := card_le_card this
    have h3 : (univ.filter (fun j : Fin m => j ≤ i)).card = i + 1 := by
      rw [show univ.filter (fun j : Fin m => j ≤ i) = Iic i by ext; simp]
      simp
    omega
  · intro hi
    by_contra hni
    have : S ⊆ univ.filter (fun j : Fin m => j < i) := fun j hj => by
      simp only [mem_filter, mem_univ, true_and]
      by_contra h
      exact hni (hS j i (not_lt.1 h) hj)
    have h2 := card_le_card this
    have h3 : (univ.filter (fun j : Fin m => j < i)).card = i := by
      rw [show univ.filter (fun j : Fin m => j < i) = Iio i by ext; simp]
      simp
    omega

/-- In a key-sorted permutation, the positions with key below `v` are the first
`#{e : key e < v}`. -/
theorem sorted_prefix {m : ℕ} (κ : Fin m → ℕ) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => κ (σ i))) (v : ℕ) (i : Fin m) :
    κ (σ i) < v ↔ (i : ℕ) < (univ.filter (fun e => κ e < v)).card := by
  have hc : (univ.filter (fun i : Fin m => κ (σ i) < v)).card = (univ.filter (fun e => κ e < v)).card := by
    apply card_bij (fun i _ => σ i)
    · intro a ha; simpa using ha
    · intro a _ b _ h; exact σ.injective h
    · intro b hb; exact ⟨σ.symm b, by simpa using hb, by simp⟩
  rw [← hc]
  have := downset_iff (univ.filter (fun i : Fin m => κ (σ i) < v))
    (fun i j hji hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact lt_of_le_of_lt (hσ hji) hi) i
  simpa using this

/-- The edges at sorted positions `[#{κ < v}, #{κ < v+1})` are exactly those with key `v`. -/
theorem sorted_block {m : ℕ} (κ : Fin m → ℕ) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => κ (σ i))) (v : ℕ) (i : Fin m) :
    κ (σ i) = v ↔ (univ.filter (fun e => κ e < v)).card ≤ (i : ℕ) ∧
      (i : ℕ) < (univ.filter (fun e => κ e < v + 1)).card := by
  rw [← sorted_prefix κ σ hσ (v + 1), ← not_lt, ← sorted_prefix κ σ hσ v]
  omega

end DirKECC1549.Asm
end

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

theorem ots_mono (D : Fin m → Fin n × Fin n) {a b : ℕ} (h : a ≤ b) : ots D a ≤ ots D b := by
  unfold ots; exact card_le_card (fun e => by simp only [mem_filter, mem_univ, true_and]; omega)

theorem tail_of_pos (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => ((D (σ i)).1 : ℕ))) (v : Fin n) (i : Fin m) :
    (D (σ i)).1 = v ↔ ots D v ≤ i ∧ (i : ℕ) < ots D (v + 1) := by
  have h := sorted_block (fun e => ((D e).1 : ℕ)) σ hσ v i
  unfold ots; rw [Fin.ext_iff]; exact h

theorem nodup_mid {α : Type*} {L P : List α} {t : α} :
    (L ++ [t] ++ P).Nodup ↔ t ∉ L ∧ t ∉ P ∧ (L ++ P).Nodup := by
  rw [List.append_assoc, List.singleton_append, List.nodup_middle, List.nodup_cons, List.mem_append]
  tauto

theorem getElem_stk {α : Type*} (L : List α) (t : α) (i : ℕ) (hi : i < (L ++ [t]).length) :
    (L ++ [t])[i] = if h : i < L.length then L[i] else t := by
  split_ifs with h
  · exact List.getElem_append_left h
  · rw [List.getElem_append_right (by omega)]; simp

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => ((D (σ i)).1 : ℕ))) (rest po : List (Fin n)) (v : Fin n)
    (ptr : Fin n → ℕ) (h : DState D σ (rest ++ [v]) po ptr) (i : Fin m) (hi : (i : ℕ) = ptr v)
    (hp : ptr v < ots D (v + 1)) (ht1 : (D (σ i)).2 ∉ rest ++ [v]) (ht2 : (D (σ i)).2 ∉ po) :
    DState D σ (rest ++ [v] ++ [(D (σ i)).2]) po
      (Function.update (Function.update ptr v (ptr v + 1)) (D (σ i)).2 (ots D (D (σ i)).2)) := by
  set t := (D (σ i)).2 with ht
  have htv : t ≠ v := fun h' => ht1 (by rw [h']; simp)
  have hv : v ∈ rest ++ [v] := by simp
  have hpv := h.plo v hv
  have hu : ∀ w, w ≠ t → w ≠ v → Function.update (Function.update ptr v (ptr v + 1)) t (ots D t) w = ptr w :=
    fun w h1 h2 => by rw [Function.update_of_ne h1, Function.update_of_ne h2]
  have huv : Function.update (Function.update ptr v (ptr v + 1)) t (ots D t) v = ptr v + 1 := by
    rw [Function.update_of_ne htv.symm, Function.update_self]
  have hut : Function.update (Function.update ptr v (ptr v + 1)) t (ots D t) t = ots D t := by
    rw [Function.update_self]
  have mem' : ∀ w, w ∈ rest ++ [v] ++ [t] ↔ w ∈ rest ++ [v] ∨ w = t := fun w => by
    rw [List.mem_append, List.mem_singleton]
  constructor
  · exact nodup_mid.2 ⟨ht1, ht2, h.nd⟩
  · intro w hw
    rcases (mem' w).1 hw with hw | rfl
    · by_cases hwv : w = v
      · subst hwv; rw [huv]; omega
      · rw [hu w (fun h' => ht1 (h' ▸ hw)) hwv]; exact h.plo w hw
    · rw [hut]
  · intro w hw
    rcases (mem' w).1 hw with hw | rfl
    · by_cases hwv : w = v
      · subst hwv; rw [huv]; omega
      · rw [hu w (fun h' => ht1 (h' ▸ hw)) hwv]; exact h.phi w hw
    · rw [hut]; exact ots_mono D (by omega)
  · intro w hw j hj1 hj2
    rcases (mem' w).1 hw with hw | rfl
    · by_cases hwv : w = v
      · subst hwv
        rw [huv] at hj2
        rcases Nat.lt_or_ge (j : ℕ) (ptr w) with hj | hj
        · rcases h.pex w hw j hj1 hj with h1 | h1
          · left; exact (mem' _).2 (Or.inl h1)
          · right; exact h1
        · have : j = i := Fin.ext (by omega)
          subst this; left; exact (mem' _).2 (Or.inr rfl)
      · rw [hu w (fun h' => ht1 (h' ▸ hw)) hwv] at hj2
        rcases h.pex w hw j hj1 hj2 with h1 | h1
        · left; exact (mem' _).2 (Or.inl h1)
        · right; exact h1
    · rw [hut] at hj2; omega
  · intro a b ha hb hab
    have hlen : (rest ++ [v] ++ [t]).length = (rest ++ [v]).length + 1 := by simp
    rw [getElem_stk (rest ++ [v]) t a ha, getElem_stk (rest ++ [v]) t b hb]
    split_ifs with h1 h2 h2
    · exact h.chain a b h1 h2 hab
    · have hb' : b = (rest ++ [v]).length := by omega
      have hlast : (rest ++ [v])[(rest ++ [v]).length - 1]'(by simp) = v := by simp
      have h3 := h.chain a ((rest ++ [v]).length - 1) h1 (by simp) (by omega)
      rw [hlast] at h3
      have htail : (D (σ i)).1 = v := (tail_of_pos D σ hσ v i).2 ⟨by omega, by omega⟩
      exact reach_trans D h3 (htail ▸ reach_edge D (σ i))
    · omega
    · exact reach_refl D t
  · intro x hx e he
    rcases h.S2 x hx e he with h1 | h1
    · left; exact (mem' _).2 (Or.inl h1)
    · right; exact h1
  · exact h.H
