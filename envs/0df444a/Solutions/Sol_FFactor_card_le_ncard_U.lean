-- Prove2me | solution 1 for FFactor.card_le_ncard_U
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:05:13.01313+00:00
-- url     : https://prove2.me/submissions/58b57017-9934-4a68-80bf-b38394012b90

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_FFactor_card_dart_fst_mem
public import Theorems.Thm_FFactor_card_inner_mem
public import Theorems.Thm_FFactor_F4
public import Theorems.Thm_FFactor_F5


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
omit [DecidableEq V]
namespace FFactor
theorem _root_.solution :
    ∑ v ∈ Sset G f U, G.degree v + ∑ v ∈ Tset G f U, (G.degree v - f v) ≤ U.ncard := by
  let F : Finset (GV G f) := (univ.filter (fun d : G.Dart => d.fst ∈ Sset G f U)).disjSum
    (univ.filter (fun p : Σ v : V, Fin (G.degree v - f v) => p.1 ∈ Tset G f U))
  have hF : (F : Set (GV G f)) ⊆ U := by
    rintro (d | p) h
    · have h' := inl_mem_disjSum.mp (mem_coe.mp h)
      exact F4 (mem_filter.mp h').2 rfl
    · have h' := inr_mem_disjSum.mp (mem_coe.mp h)
      obtain ⟨v, i⟩ := p
      exact F5 (mem_filter.mp h').2 i
  have := Set.ncard_le_ncard hF (Set.toFinite U)
  rw [Set.ncard_coe_finset, card_disjSum, card_dart_fst_mem, card_inner_mem] at this
  exact this
end FFactor
