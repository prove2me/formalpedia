-- Prove2me | solution 1 for DirKECC1549.Asm.dstate_finish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:17:51.861343+00:00
-- url     : https://prove2.me/submissions/7d54f86a-658a-4fb0-9dd7-e98b6d8272fc

import Definitions.Def_DirKECC1549_Impl_SccDfs
import Theorems.Thm_DirKECC1549_Asm_dfsH_finish

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

/-- `H` only depends on the positions of finished vertices. -/
theorem dfsH_congr (D : Fin m → Fin n × Fin n) (fin : Finset (Fin n)) (pos pos' : Fin n → ℕ)
    (h : DfsH D fin pos) (he : ∀ x ∈ fin, pos' x = pos x) : DfsH D fin pos' := by
  intro x hx y hxy hyx
  rcases h x hx y hxy hyx with ⟨h1, h2⟩ | ⟨g, h1, h2, h3 | ⟨h4, h5, h6⟩⟩
  · left; exact ⟨h1, by rw [he y h1, he x hx]; exact h2⟩
  · right; exact ⟨g, h1, h2, Or.inl h3⟩
  · right; exact ⟨g, h1, h2, Or.inr ⟨h4, h5, by rw [he y h5, he g h4]; exact h6⟩⟩

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

theorem tail_of_pos (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => ((D (σ i)).1 : ℕ))) (v : Fin n) (i : Fin m) :
    (D (σ i)).1 = v ↔ ots D v ≤ i ∧ (i : ℕ) < ots D (v + 1) := by
  have h := sorted_block (fun e => ((D e).1 : ℕ)) σ hσ v i
  unfold ots; rw [Fin.ext_iff]; exact h

theorem nodup_mid {α : Type*} {L P : List α} {t : α} :
    (L ++ [t] ++ P).Nodup ↔ t ∉ L ∧ t ∉ P ∧ (L ++ P).Nodup := by
  rw [List.append_assoc, List.singleton_append, List.nodup_middle, List.nodup_cons, List.mem_append]
  tauto

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => ((D (σ i)).1 : ℕ))) (rest po : List (Fin n)) (v : Fin n)
    (ptr : Fin n → ℕ) (h : DState D σ (rest ++ [v]) po ptr) (hp : ots D (v + 1) ≤ ptr v) :
    DState D σ rest (po ++ [v]) ptr := by
  have hnd := h.nd
  have hvr : v ∉ rest := (nodup_mid.1 (by simpa using hnd)).1
  have hvp : v ∉ po := (nodup_mid.1 (by simpa using hnd)).2.1
  have hmem : ∀ w, w ∈ rest ++ [v] ∨ w ∈ po → w ∈ rest ∨ w ∈ po ++ [v] := fun w hw => by
    simp only [List.mem_append, List.mem_singleton] at hw ⊢; tauto
  -- all out-edges of `v` are explored
  have hout : ∀ e : Fin m, (D e).1 = v → (D e).2 ∈ rest ++ [v] ∨ (D e).2 ∈ po := by
    intro e he
    have h1 : (D (σ (σ.symm e))).1 = v := by simpa using he
    obtain ⟨a1, a2⟩ := (tail_of_pos D σ hσ v (σ.symm e)).1 h1
    have := h.pex v (by simp) (σ.symm e) a1 (by have := h.phi v (by simp); omega)
    simpa using this
  constructor
  · have := (nodup_mid.1 (by simpa using hnd)).2.2
    rw [List.nodup_append] at this ⊢
    refine ⟨this.1, ?_, ?_⟩
    · rw [List.nodup_append]
      exact ⟨this.2.1, by simp, by intro a ha b hb hab; simp at hb; subst hb; subst hab; exact hvp ha⟩
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact this.2.2 a ha a hb rfl
      · exact hvr ha
  · exact fun w hw => h.plo w (by simp [hw])
  · exact fun w hw => h.phi w (by simp [hw])
  · intro w hw j hj1 hj2
    exact hmem _ (h.pex w (by simp [hw]) j hj1 hj2)
  · intro a b ha hb hab
    have := h.chain a b (by simp; omega) (by simp; omega) hab
    rwa [List.getElem_append_left ha, List.getElem_append_left hb] at this
  · intro x hx e he
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hmem _ (h.S2 x hx e he)
    · exact hmem _ (hout e he)
  · have hH := dfsH_finish D po.toFinset (fun w => po.idxOf w) (rest ++ [v]).toFinset v
      (by simpa using hvp) (by simp) (fun x hx => by
        simp only [List.mem_toFinset] at hx ⊢
        intro hx2
        exact (List.nodup_append.1 hnd).2.2 x hx2 x hx rfl) h.H
      (fun e he => by
        simp only [mem_insert, List.mem_toFinset] at he ⊢
        rcases he with he | he
        · rcases hout e he with h1 | h1
          · right; exact h1
          · left; right; exact h1
        · rcases h.S2 _ he e rfl with h1 | h1
          · right; exact h1
          · left; right; exact h1)
      (fun g hg => by
        simp only [List.mem_toFinset] at hg
        obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hg
        have := h.chain a ((rest ++ [v]).length - 1) ha (by simp) (by simp at ha ⊢; omega)
        simpa using this)
      po.length (fun x hx => by simpa using List.idxOf_lt_length_of_mem (by simpa using hx))
    have hfs : insert v po.toFinset = (po ++ [v]).toFinset := by
      ext x; simp only [mem_insert, List.mem_toFinset, List.mem_append, List.mem_singleton]; tauto
    rw [hfs] at hH
    apply dfsH_congr D _ _ _ hH
    intro x hx
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · rw [Function.update_of_ne (by rintro rfl; exact hvp hx), List.idxOf_append_of_mem hx]
    · rw [Function.update_self, List.idxOf_append_of_notMem hvp]; simp
