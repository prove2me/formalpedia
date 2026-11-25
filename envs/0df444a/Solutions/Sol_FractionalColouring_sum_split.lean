-- Prove2me | solution 1 for FractionalColouring.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:14.93566+00:00
-- url     : https://prove2.me/submissions/7ff7b454-0e93-4379-b0ab-14cd4a5b98cb

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Theorems.Thm_FiniteLP_toE_apply
public import Theorems.Thm_Mycielski_apex_adj_shadow
public import Theorems.Thm_Mycielski_not_shadow_adj_shadow
public import Theorems.Thm_Mycielski_original_adj_original
public import Theorems.Thm_Mycielski_original_adj_shadow
public import Theorems.Thm_Mycielski_shadow_adj_apex
public import Theorems.Thm_Mycielski_shadow_adj_original
attribute [local simp] FiniteLP.toE_apply
attribute [local simp] Mycielski.apex_adj_shadow
attribute [local simp] Mycielski.not_shadow_adj_shadow
attribute [local simp] Mycielski.original_adj_original
attribute [local simp] Mycielski.original_adj_shadow
attribute [local simp] Mycielski.shadow_adj_apex
attribute [local simp] Mycielski.shadow_adj_original



set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
namespace FractionalColouring
theorem _root_.solution (S : Finset (Vertex V)) (h : Vertex V → ℝ) :
    ∑ u ∈ S, h u = (if none ∈ S then h none else 0) +
      ∑ v ∈ univ.filter (fun v => original v ∈ S), h (original v) +
      ∑ v ∈ univ.filter (fun v => shadow v ∈ S), h (shadow v) := by
  have hS : ∑ u ∈ S, h u = ∑ u, if u ∈ S then h u else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext u; simp
  rw [hS, Fintype.sum_option, Fintype.sum_prod_type, Finset.sum_filter, Finset.sum_filter]
  simp only [Fintype.sum_bool, Finset.sum_add_distrib, original, shadow]
  exact (add_assoc (G := ℝ) _ _ _).symm.trans (add_right_comm _ _ _)
end FractionalColouring
