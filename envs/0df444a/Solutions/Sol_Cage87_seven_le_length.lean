-- Prove2me | solution 1 for Cage87.seven_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:28:12.278035+00:00
-- url     : https://prove2.me/submissions/dc1233ed-4503-40da-91d2-7e560301e4c8

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge
public import Theorems.Thm_Cage87_G_adj
public import Theorems.Thm_Cage87_branch_disjoint
public import Theorems.Thm_Cage87_mem_branch_one
public import Theorems.Thm_Cage87_mem_branch_two
public import Theorems.Thm_Cage87_mem_branch_three
attribute [local simp] Cage87.G_adj

set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
namespace Cage87
theorem _root_.solution {a : Fin 768} (w : G.Walk a a) (hw : w.IsCycle) : 7 ≤ w.length := by
  by_contra hlt
  have h3 := hw.three_le_length
  have hadj : ∀ i < w.length, (w.getVert (i + 1)).val ∈ nb adj (w.getVert i).val :=
    fun i hi => w.adj_getVert_succ hi
  have hadj' : ∀ i < w.length, (w.getVert i).val ∈ nb adj (w.getVert (i + 1)).val :=
    fun i hi => (w.adj_getVert_succ hi).symm
  have hinj : ∀ i j, i ≤ w.length - 1 → j ≤ w.length - 1 →
      (w.getVert i).val = (w.getVert j).val → i = j :=
    fun i j hi hj h => hw.getVert_injOn' hi hj (Fin.ext h)
  have h0 : (w.getVert 0).val = a.val := by rw [Walk.getVert_zero]
  have hl : (w.getVert w.length).val = a.val := by rw [Walk.getVert_length]
  have hv := a.2
  generalize w.length = l at *
  have hx : (w.getVert 1).val ∈ nb adj a.val := h0 ▸ hadj 0 (by omega)
  have hy : (w.getVert (l - 1)).val ∈ nb adj a.val := by
    have := hadj' (l - 1) (by omega)
    rwa [show l - 1 + 1 = l by omega, hl] at this
  have hxy : (w.getVert 1).val ≠ (w.getVert (l - 1)).val := fun h => by
    have := hinj 1 (l - 1) (by omega) (by omega) h; omega
  have hne : ∀ i j, i ≤ l - 1 → j ≤ l - 1 → i ≠ j → (w.getVert i).val ≠ (w.getVert j).val :=
    fun i j hi hj hij h => hij (hinj i j hi hj h)
  have hna : ∀ i, 1 ≤ i → i ≤ l - 1 → (w.getVert i).val ≠ a.val := fun i h1 h2 h => by
    have := hinj i 0 h2 (by omega) (h.trans h0.symm); omega
  interval_cases l
  · -- l = 3: v₁ is in both branches
    exact branch_disjoint hv hx hy hxy (mem_branch_one _ _)
      (mem_branch_two (hadj' 1 (by omega)) (hna 1 (by omega) (by omega)))
  · -- l = 4: v₂
    exact branch_disjoint hv hx hy hxy (mem_branch_two (hadj 1 (by omega)) (hna 2 (by omega) (by omega)))
      (mem_branch_two (hadj' 2 (by omega)) (hna 2 (by omega) (by omega)))
  · -- l = 5: v₂, through v₁ and through v₄, v₃
    exact branch_disjoint hv hx hy hxy (mem_branch_two (hadj 1 (by omega)) (hna 2 (by omega) (by omega)))
      (mem_branch_three (hadj' 3 (by omega)) (hna 3 (by omega) (by omega)) (hadj' 2 (by omega))
        (hne 2 4 (by omega) (by omega) (by omega)))
  · -- l = 6: v₃, through v₁, v₂ and through v₅, v₄
    exact branch_disjoint hv hx hy hxy
      (mem_branch_three (hadj 1 (by omega)) (hna 2 (by omega) (by omega)) (hadj 2 (by omega))
        (hne 3 1 (by omega) (by omega) (by omega)))
      (mem_branch_three (hadj' 4 (by omega)) (hna 4 (by omega) (by omega)) (hadj' 3 (by omega))
        (hne 3 5 (by omega) (by omega) (by omega)))
end Cage87
