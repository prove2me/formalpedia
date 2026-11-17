-- Prove2me | solution 1 for DirKECC1549.Asm.fstate_visit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T07:05:03.744931+00:00
-- url     : https://prove2.me/submissions/705f8a4a-d7d3-4e46-a1d3-32fd255b7b86

import Definitions.Def_DirKECC1549_Impl_FlowBfs

set_option autoImplicit false

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (H : Fin m → Fin n × Fin n) (z : Fin n) (q : List (Fin n)) (h : ℕ)
    (par : Fin n → Fin m) (hS : FState H z q h par) (hh : h < q.length) (e : Fin m)
    (he1 : (H e).1 = q[h]) (hy : (H e).2 ∉ q) :
    FState H z (q ++ [(H e).2]) h (Function.update par (H e).2 e) := by
  set y := (H e).2
  have hpar : ∀ u ∈ q, Function.update par y e u = par u := fun u hu =>
    Function.update_of_ne (by rintro rfl; exact hy hu) _ _
  have hle' : h ≤ (q ++ [y]).length := by simp; omega
  exact
  { nd := List.nodup_append.2 ⟨hS.nd, List.nodup_singleton y, by
      intro a ha b hb hab; simp at hb; subst hb; subst hab; exact hy ha⟩
    hd := by
      obtain ⟨h0, h1⟩ := hS.hd
      exact ⟨by simp, by rw [List.getElem_append_left h0]; exact h1⟩
    hle := hle'
    parent := fun i hi h0 => by
      simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_ge i q.length with hi' | hi'
      · rw [List.getElem_append_left hi', hpar _ (List.getElem_mem hi')]
        obtain ⟨a1, j, hj, a2⟩ := hS.parent i hi' h0
        exact ⟨a1, j, hj, by rw [List.getElem_append_left (by omega)]; exact a2⟩
      · have : i = q.length := by omega
        subst this
        have hgl : (q ++ [y])[q.length] = y := by simp
        rw [hgl, Function.update_self]
        exact ⟨rfl, h, hh, by rw [List.getElem_append_left hh]; exact he1⟩
    closed := fun i hi e' he' => by
      rw [List.getElem_append_left (by have := hS.hle; omega)] at he'
      exact List.mem_append_left _ (hS.closed i hi e' he') }
