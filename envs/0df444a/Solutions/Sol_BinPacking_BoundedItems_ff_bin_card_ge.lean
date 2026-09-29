-- Prove2me | solution 1 for BinPacking.BoundedItems.ff_bin_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:54:16.077175+00:00
-- url     : https://prove2.me/submissions/509f5506-f8d6-4629-bcf0-397296eb8509

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

/-- Invariant: all items are at most `1/m`, and every bin but the last has at least `m` items. -/
def aux_ffb_Good (m : ℕ) (P : List (List ℝ)) : Prop :=
  (∀ B ∈ P, ∀ x ∈ B, x ≤ 1 / (m : ℝ)) ∧ ∀ B ∈ P.dropLast, m ≤ B.length

theorem aux_ffb_insert_ne_nil (a : ℝ) (P : List (List ℝ)) : ffInsert a P ≠ [] := by
  cases P with
  | nil => simp [ffInsert]
  | cons B Bs =>
    unfold ffInsert
    split_ifs <;> simp

theorem aux_ffb_dropLast_cons_sub (B : List ℝ) (Bs : List (List ℝ)) :
    ∀ C ∈ Bs.dropLast, C ∈ (B :: Bs).dropLast := by
  intro C hC
  cases Bs with
  | nil => simp at hC
  | cons D Ds =>
    rw [List.dropLast_cons_cons]
    exact List.mem_cons_of_mem _ hC

theorem aux_ffb_nonfit (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : a ≤ 1 / (m : ℝ))
    (B : List ℝ) (hB : ∀ x ∈ B, x ≤ 1 / (m : ℝ)) (h : ¬ level B + a ≤ 1) :
    m ≤ B.length := by
  by_contra hlt
  push Not at hlt
  apply h
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : level B ≤ B.length • (1 / (m : ℝ)) := List.sum_le_card_nsmul B _ hB
  rw [nsmul_eq_mul] at h1
  have h2 : ((B.length : ℝ) + 1) ≤ m := by exact_mod_cast hlt
  have h3 : (B.length : ℝ) * (1 / (m : ℝ)) + 1 / (m : ℝ) ≤ 1 := by
    rw [← add_one_mul, mul_one_div, div_le_one hmpos]
    exact h2
  linarith

theorem aux_ffb_insert (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : a ≤ 1 / (m : ℝ)) :
    ∀ P : List (List ℝ), aux_ffb_Good m P → aux_ffb_Good m (ffInsert a P)
  | [], _ => by
    refine ⟨?_, ?_⟩
    · intro B hB x hx
      simp [ffInsert] at hB
      subst hB
      simp at hx
      rw [hx]; exact ha
    · intro B hB
      simp [ffInsert] at hB
  | B :: Bs, hP => by
    obtain ⟨hP1, hP2⟩ := hP
    by_cases h : level B + a ≤ 1
    · have e : ffInsert a (B :: Bs) = (B ++ [a]) :: Bs := by
        simp [ffInsert, h]
      rw [e]
      refine ⟨?_, ?_⟩
      · intro C hC x hx
        rcases List.mem_cons.mp hC with hC | hC
        · subst hC
          rcases List.mem_append.mp hx with hx | hx
          · exact hP1 B (List.mem_cons_self) x hx
          · simp at hx; rw [hx]; exact ha
        · exact hP1 C (List.mem_cons_of_mem _ hC) x hx
      · intro C hC
        cases Bs with
        | nil => simp at hC
        | cons D Ds =>
          rw [List.dropLast_cons_cons] at hC
          rw [List.dropLast_cons_cons] at hP2
          rcases List.mem_cons.mp hC with hC | hC
          · subst hC
            have := hP2 B List.mem_cons_self
            simp; omega
          · exact hP2 C (List.mem_cons_of_mem _ hC)
    · have e : ffInsert a (B :: Bs) = B :: ffInsert a Bs := by
        simp [ffInsert, h]
      rw [e]
      have hBs : aux_ffb_Good m Bs :=
        ⟨fun C hC => hP1 C (List.mem_cons_of_mem _ hC),
         fun C hC => hP2 C (aux_ffb_dropLast_cons_sub B Bs C hC)⟩
      obtain ⟨ih1, ih2⟩ := aux_ffb_insert m hm a ha Bs hBs
      have hlen : m ≤ B.length := aux_ffb_nonfit m hm a ha B (hP1 B List.mem_cons_self) h
      refine ⟨?_, ?_⟩
      · intro C hC x hx
        rcases List.mem_cons.mp hC with hC | hC
        · subst hC; exact hP1 C List.mem_cons_self x hx
        · exact ih1 C hC x hx
      · intro C hC
        obtain ⟨D, Ds, hDs⟩ := List.exists_cons_of_ne_nil (aux_ffb_insert_ne_nil a Bs)
        rw [hDs, List.dropLast_cons_cons] at hC
        rw [hDs] at ih2
        rcases List.mem_cons.mp hC with hC | hC
        · subst hC; exact hlen
        · exact ih2 C hC

theorem aux_ffb_foldl (m : ℕ) (hm : 1 ≤ m) :
    ∀ (L : List ℝ) (P : List (List ℝ)), (∀ a ∈ L, a ≤ 1 / (m : ℝ)) →
      aux_ffb_Good m P → aux_ffb_Good m (L.foldl (fun P a => ffInsert a P) P)
  | [], P, _, hP => by simpa using hP
  | a :: L, P, hL, hP => by
    rw [List.foldl_cons]
    exact aux_ffb_foldl m hm L _ (fun b hb => hL b (List.mem_cons_of_mem _ hb))
      (aux_ffb_insert m hm a (hL a List.mem_cons_self) P hP)

end BinPacking.BoundedItems

open BinPacking.BoundedItems

theorem solution (m : ℕ) (hm : 1 ≤ m) (L : List ℝ) (hL : IsList L)
    (hLm : ∀ a ∈ L, a ≤ 1 / (m : ℝ)) :
    ∀ B ∈ (ffPack L).dropLast, m ≤ B.length := by
  have h := aux_ffb_foldl m hm L [] hLm ⟨by simp, by simp⟩
  exact h.2
