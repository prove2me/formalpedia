-- Prove2me | solution 1 for FFactor.notMem_U_of_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:06:34.363168+00:00
-- url     : https://prove2.me/submissions/ee1c2828-d393-4869-9e9b-1ce1e6753afa

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_FFactor_F2
public import Theorems.Thm_FFactor_F3
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_notMem_S_of_notMem_union
attribute [local simp] FFactor.home_inl



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution {hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x} {a : GV G f}
    (ha : home G f U a ∉ Sset G f U ∪ Tset G f U) : a ∉ U := by
  have hT := notMem_T_of_notMem_union ha
  have hS := notMem_S_of_notMem_union ha
  rcases a with d | ⟨r, i⟩
  · rw [home_inl] at hT hS
    by_cases h : d.fst ∈ Tset G f U
    · exact F2 hmin h rfl
    · rw [if_neg h] at hT hS
      exact F3 hmin hT hS rfl
  · exact F1 hmin hT i
end FFactor
