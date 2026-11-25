-- Prove2me | solution 1 for FractionalColouring.le_fracChromaticNumber_mycielski
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:54:05.84481+00:00
-- url     : https://prove2.me/submissions/3df4a2cf-e04b-4635-80ee-30187e013ba2

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Theorems.Thm_FractionalColouring_original_mem_lift
public import Theorems.Thm_FractionalColouring_shadow_mem_lift
public import Theorems.Thm_FractionalColouring_none_not_mem_lift
public import Theorems.Thm_FractionalColouring_original_mem_liftApex
public import Theorems.Thm_FractionalColouring_shadow_not_mem_liftApex
public import Theorems.Thm_FractionalColouring_none_mem_liftApex
public import Theorems.Thm_FractionalColouring_original_not_mem_shadows
public import Theorems.Thm_FractionalColouring_shadow_mem_shadows
public import Theorems.Thm_FractionalColouring_none_not_mem_shadows
public import Theorems.Thm_FractionalColouring_sum_mycielskiClique
public import Theorems.Thm_FractionalColouring_isFracClique_mycielskiClique
public import Theorems.Thm_FiniteLP_toE_apply
public import Theorems.Thm_FractionalColouring_IsFracClique_sum_le_fracChromaticNumber
public import Theorems.Thm_FractionalColouring_exists_fracClique_eq
public import Theorems.Thm_FractionalColouring_le_mul_fracChromaticNumber
public import Theorems.Thm_FractionalColouring_one_le_fracChromaticNumber
public import Theorems.Thm_FractionalColouring_sum_le_mul_of_indep
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


attribute [local simp] FractionalColouring.original_mem_lift
attribute [local simp] FractionalColouring.shadow_mem_lift
attribute [local simp] FractionalColouring.none_not_mem_lift
attribute [local simp] FractionalColouring.original_mem_liftApex
attribute [local simp] FractionalColouring.shadow_not_mem_liftApex
attribute [local simp] FractionalColouring.none_mem_liftApex
attribute [local simp] FractionalColouring.original_not_mem_shadows
attribute [local simp] FractionalColouring.shadow_mem_shadows
attribute [local simp] FractionalColouring.none_not_mem_shadows

set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution [Nonempty V] :
    fracChromaticNumber G + 1 / fracChromaticNumber G ≤ fracChromaticNumber (graph G) := by
  obtain ⟨g, hg, hga⟩ := exists_fracClique_eq (G := G)
  set a := fracChromaticNumber G with ha_def
  have ha : 1 ≤ a := one_le_fracChromaticNumber
  have ha0 : 0 < a := by linarith
  have hM : IsFracClique (graph G) (mycielskiClique g a) :=
    isFracClique_mycielskiClique hg ha fun x hx T c hc hT => by
      have := sum_le_mul_of_indep hg.1 hT hx
      exact le_mul_fracChromaticNumber hc fun y hy => sum_le_mul_of_indep hg.1 hT hy
  have hsum := hM.sum_le_fracChromaticNumber
  rw [show (∑ u, mycielskiClique g a u) = ∑ u ∈ univ, mycielskiClique g a u from rfl,
    sum_mycielskiClique] at hsum
  simp only [mem_univ, ite_true, Finset.filter_true] at hsum
  rw [hga] at hsum
  have : 1 / a + (1 - 1 / a) * a + a / a = a + 1 / a := by field_simp; ring
  linarith
end FractionalColouring
