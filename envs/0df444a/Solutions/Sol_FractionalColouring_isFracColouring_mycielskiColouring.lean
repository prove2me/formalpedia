-- Prove2me | solution 1 for FractionalColouring.isFracColouring_mycielskiColouring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:53:43.331794+00:00
-- url     : https://prove2.me/submissions/8f5c8e0a-8fbe-4573-9345-d42e1075a77d

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
public import Theorems.Thm_FractionalColouring_isIndepSet_lift
public import Theorems.Thm_FractionalColouring_isIndepSet_liftApex
public import Theorems.Thm_FractionalColouring_isIndepSet_shadows
public import Theorems.Thm_FractionalColouring_mycielskiColouring_cover
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
theorem _root_.solution {x : Finset V → ℝ} (hx : IsFracColouring G x)
    {t : ℝ} (ht : 1 ≤ t) (hxt : ∑ s, x s = t) :
    IsFracColouring (graph G) (mycielskiColouring x t) := by
  have ht0 : 0 < t := by linarith
  have hc : 0 ≤ (t - 1) / t := div_nonneg (by linarith) ht0.le
  refine ⟨fun S => ?_, fun S hS => ?_, fun u => ?_⟩
  · unfold mycielskiColouring
    have h1 : ∀ s, 0 ≤ (if S = lift s then x s * ((t - 1) / t) else 0) := fun s => by
      split_ifs
      exacts [mul_nonneg (hx.1 s) hc, le_rfl]
    have h2 : ∀ s, 0 ≤ (if S = liftApex s then x s / t else 0) := fun s => by
      split_ifs
      exacts [div_nonneg (hx.1 s) ht0.le, le_rfl]
    have h3 : 0 ≤ (if S = shadows then 1 / t else 0) := by
      split_ifs
      exacts [div_nonneg zero_le_one ht0.le, le_rfl]
    exact add_nonneg (Finset.sum_nonneg fun s _ => add_nonneg (h1 s) (h2 s)) h3
  · unfold mycielskiColouring
    have h3 : (if S = shadows then 1 / t else 0) = 0 := by
      rw [if_neg]; rintro rfl; exact hS isIndepSet_shadows
    rw [h3, add_zero]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hxs : ¬ G.IsIndepSet (s : Set V) → x s = 0 := hx.2.1 s
    by_cases hs : G.IsIndepSet (s : Set V)
    · rw [if_neg (by rintro rfl; exact hS (isIndepSet_lift hs)),
        if_neg (by rintro rfl; exact hS (isIndepSet_liftApex hs))]
      simp
    · simp [hxs hs]
  · rw [mycielskiColouring_cover]
    rcases u with _ | ⟨v, _ | _⟩
    · -- the apex
      simp only [none_not_mem_lift, none_mem_liftApex, none_not_mem_shadows, if_false, if_true,
        zero_add, add_zero]
      rw [← Finset.sum_div, hxt, div_self ht0.ne']
    · -- an original vertex
      have h := hx.2.2 v
      simp only [show (some (v, false) : Vertex V) = original v from rfl, original_mem_lift,
        original_mem_liftApex, original_not_mem_shadows, if_false, add_zero]
      rw [Finset.sum_filter] at h
      calc (1 : ℝ) ≤ ∑ s, if v ∈ s then x s else 0 := h
        _ = ∑ s, ((if v ∈ s then x s * ((t - 1) / t) else 0) + if v ∈ s then x s / t else 0) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs
          · field_simp; ring
          · simp
    · -- a shadow vertex
      have h := hx.2.2 v
      simp only [show (some (v, true) : Vertex V) = shadow v from rfl, shadow_mem_lift,
        shadow_not_mem_liftApex, shadow_mem_shadows, if_false, if_true, add_zero]
      rw [Finset.sum_filter] at h
      have : (t - 1) / t ≤ ∑ s, if v ∈ s then x s * ((t - 1) / t) else 0 := by
        rw [show (∑ s, if v ∈ s then x s * ((t - 1) / t) else 0) =
          (∑ s, if v ∈ s then x s else 0) * ((t - 1) / t) by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp]
        exact le_mul_of_one_le_left hc h
      have h1 : (t - 1) / t + 1 / t = 1 := by field_simp; ring
      linarith
end FractionalColouring
