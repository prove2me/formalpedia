-- Prove2me | solution 1 for FFactor.exists_factor_of_condition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:16:21.095022+00:00
-- url     : https://prove2.me/submissions/8e0e8a39-cc86-450d-99f5-cbb8d5c1fb60

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_FFactor_ncard_odd_le
public import Theorems.Thm_FFactor_card_inner_mem
public import Theorems.Thm_FFactor_card_dart_fst_snd_mem
public import Theorems.Thm_FFactor_card_adj_split
public import Theorems.Thm_FFactor_card_le_ncard_U
public import Theorems.Thm_FFactor_not_isTutteViolator_iff_le
public import Theorems.Thm_FFactor_disjoint_Sset_Tset
public import Theorems.Thm_FFactor_exists_factor_of_matching
public import Theorems.Thm_FFactor_exists_min_violator
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
variable (G f)
namespace FFactor
theorem _root_.solution
    (h : ∀ S T : Finset V, Disjoint S T → (oddCnt G f S T : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ)) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v, #{u | H.Adj v u} = f v := by
  have hf : ∀ v, f v ≤ G.degree v := by
    intro v
    have h1 := h ∅ {v} (disjoint_empty_left _)
    have h2 := card_adj_split (G := G) v ∅
    simp only [sum_empty, sum_singleton, zero_sub] at h1
    have h3 : (#{u | G.Adj v u ∧ u ∈ (∅ : Finset V)}) = 0 := by simp
    have h4 : (0 : ℤ) ≤ oddCnt G f ∅ {v} := Nat.cast_nonneg _
    omega
  by_cases hM : ∃ M : (gadget G f).Subgraph, M.IsPerfectMatching
  · obtain ⟨M, hM⟩ := hM
    exact exists_factor_of_matching hf M hM
  exfalso
  have hviol : ∃ U, (gadget G f).IsTutteViolator U := by
    by_contra hno
    push Not at hno
    exact hM (tutte.mpr hno)
  obtain ⟨U, hU, hmin⟩ := exists_min_violator _ hviol
  have hodd := ncard_odd_le hmin hf
  have hUc := card_le_ncard_U (U := U)
  have hU' := (not_isTutteViolator_iff_le).mp hU
  have hyp := h (Sset G f U) (Tset G f U) disjoint_Sset_Tset
  rw [card_dart_fst_snd_mem, card_inner_mem] at hodd
  have hsplit : ∀ t, (#{u | G.Adj t u ∧ u ∈ Sset G f U} : ℤ) +
      (#{u | G.Adj t u ∧ u ∉ Sset G f U} : ℤ) = G.degree t := by
    intro t; exact_mod_cast card_adj_split t (Sset G f U)
  have hsub : ∀ s : Finset V, ((∑ v ∈ s, (G.degree v - f v) : ℕ) : ℤ) =
      ∑ v ∈ s, ((G.degree v : ℤ) - f v) := by
    intro s
    rw [Nat.cast_sum]
    exact sum_congr rfl (fun v _ => Nat.cast_sub (hf v))
  have hodd' : ((del (gadget G f) U).oddComponents.ncard : ℤ) ≤
      oddCnt G f (Sset G f U) (Tset G f U) +
      ∑ t ∈ Tset G f U, (#{u | G.Adj t u ∧ u ∈ Sset G f U} : ℤ) +
      ∑ v ∈ Sset G f U, ((G.degree v : ℤ) - f v) := by
    rw [← hsub]; exact_mod_cast hodd
  have hUc' : ∑ v ∈ Sset G f U, (G.degree v : ℤ) + ∑ v ∈ Tset G f U, ((G.degree v : ℤ) - f v) ≤
      U.ncard := by
    rw [← hsub]; exact_mod_cast hUc
  have hU'' : (U.ncard : ℤ) < (del (gadget G f) U).oddComponents.ncard := by exact_mod_cast hU'
  have hT : ∑ t ∈ Tset G f U, (#{u | G.Adj t u ∧ u ∈ Sset G f U} : ℤ) +
      ∑ t ∈ Tset G f U, (#{u | G.Adj t u ∧ u ∉ Sset G f U} : ℤ) =
      ∑ t ∈ Tset G f U, (G.degree t : ℤ) := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun t _ => hsplit t)
  simp only [sum_sub_distrib] at hodd' hUc'
  linarith
end FFactor
