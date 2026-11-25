-- Prove2me | solution 1 for DiracCycle.exists_isCycle_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:53:10.587903+00:00
-- url     : https://prove2.me/submissions/2671d3d9-5b3f-40de-85f6-d9c97a4c09ba

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Theorems.Thm_Hamiltonicity_CycArr_eq_iff
public import Theorems.Thm_Hamiltonicity_CycArr_eq_mod
public import Theorems.Thm_Hamiltonicity_CycArr_pos
public import Theorems.Thm_Hamiltonicity_edges_walkOf
public import Theorems.Thm_Hamiltonicity_support_walkOf


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}
namespace DiracCycle
theorem _root_.solution {m : ℕ} {f : ℕ → V} (h : CycArr G m f) :
    ∃ c : G.Walk (f 0) (f 0), c.IsCycle ∧ ∀ i, f i ∈ c.support := by
  have hm := h.three_le
  have hend : f (m - 1 + 1) = f 0 := by
    rw [show m - 1 + 1 = 0 + m by omega, h.periodic]
  let p := (walkOf G (fun i => f (i + 1)) (fun i => h.adj (i + 1)) (m - 1)).copy rfl hend
  refine ⟨Walk.cons (h.adj 0) p, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    constructor
    · rw [Walk.isPath_def, Walk.support_copy, support_walkOf]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj hij
      simp only [List.mem_range] at hi hj
      rw [h.eq_iff] at hij
      have := Nat.ModEq.add_right_cancel' 1 hij
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    · rw [Walk.edges_copy, edges_walkOf]
      simp only [List.mem_map, List.mem_range, not_exists, not_and]
      intro i hi he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := h.inj _ _ (by omega) (by omega) h1
        omega
      · have := h.inj _ _ (by omega) (by omega) h1
        have h3 : i = 0 := by omega
        subst h3
        have := h.inj _ _ (by omega) (by omega) h2
        omega
  · intro i
    rw [h.eq_mod i, Walk.support_cons, List.mem_cons]
    have hlt : i % m < m := Nat.mod_lt _ h.pos
    by_cases h0 : i % m = 0
    · left; rw [h0]
    · right
      rw [Walk.support_copy, support_walkOf, List.mem_map]
      exact ⟨i % m - 1, List.mem_range.2 (by omega), by rw [show i % m - 1 + 1 = i % m by omega]⟩
end DiracCycle
