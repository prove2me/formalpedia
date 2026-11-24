-- Prove2me | solution 1 for FFactor.card_home_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:04:42.840136+00:00
-- url     : https://prove2.me/submissions/57864fd0-5634-4390-bbef-6c42b9d9f7ee

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_FFactor_card_filter_sum_type
public import Theorems.Thm_FFactor_card_inner_fiber
public import Theorems.Thm_FFactor_card_dart_snd_fst
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.gadget_adj_inl_inl
attribute [local simp] FFactor.gadget_adj_inl_inr
attribute [local simp] FFactor.gadget_adj_inr_inl
attribute [local simp] FFactor.gadget_adj_inr_inr
attribute [local simp] FFactor.home_inl
attribute [local simp] FFactor.home_inr
attribute [local simp] FFactor.mem_del_verts



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution {r : V} (hr : r ∉ Tset G f U) :
    #{a : GV G f | home G f U a = r} =
      G.degree r + #{t ∈ Tset G f U | G.Adj r t} + (G.degree r - f r) := by
  rw [card_filter_sum_type]
  have e1 : #{b : Σ v : V, Fin (G.degree v - f v) | home G f U (.inr b) = r} =
      G.degree r - f r := by
    rw [← card_inner_fiber r]; congr 1
  have e2 : #{d : G.Dart | home G f U (.inl d) = r} =
      G.degree r + #{t ∈ Tset G f U | G.Adj r t} := by
    rw [← card_dart_snd_fst r (Tset G f U), ← G.dart_fst_fiber_card_eq_degree r,
      ← card_union_of_disjoint]
    · congr 1
      ext d
      simp only [mem_filter, mem_univ, true_and, mem_union]
      rw [home_inl]
      split_ifs with h
      · constructor
        · intro h'; exact Or.inr ⟨h, h'⟩
        · rintro (h' | h')
          · exact absurd (h' ▸ h) hr
          · exact h'.2
      · constructor
        · intro h'; exact Or.inl h'
        · rintro (h' | h')
          · exact h'
          · exact absurd h'.1 h
    · rw [Finset.disjoint_left]
      intro d h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      exact hr (h1 ▸ h2.1)
  rw [e1, e2]
end FFactor
