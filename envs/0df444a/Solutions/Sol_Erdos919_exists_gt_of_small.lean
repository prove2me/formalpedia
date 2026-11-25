-- Prove2me | solution 1 for Erdos919.exists_gt_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:36:09.602056+00:00
-- url     : https://prove2.me/submissions/8e1c28b6-3a41-4a2b-8b1f-ff70f4de8232

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_W
public import Theorems.Thm_Erdos919_aleph1_lt_aleph2
public import Theorems.Thm_Erdos919_mk_Iic_W

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {J : Type u} (f : J → W.{u}) (hJ : #J ≤ ℵ₁) :
    ∃ u, ∀ j, f j < u := by
  by_contra h
  push Not at h
  have hsub : (univ : Set W) ⊆ ⋃ j, Iic (f j) := fun u _ => by
    obtain ⟨j, hj⟩ := h u
    exact mem_iUnion.2 ⟨j, hj⟩
  have h1 : #W.{u} ≤ ℵ₁ := by
    calc #W.{u} = #(univ : Set W) := mk_univ.symm
      _ ≤ #(⋃ j, Iic (f j)) := mk_le_mk_of_subset hsub
      _ ≤ #J * ⨆ j, #(Iic (f j)) := mk_iUnion_le _
      _ ≤ ℵ₁ * ℵ₁ := mul_le_mul' hJ (ciSup_le' fun j => mk_Iic_W (f j))
      _ = ℵ₁ := mul_eq_self (aleph0_le_aleph 1)
  rw [mk_W] at h1
  exact absurd h1 (not_le.2 aleph1_lt_aleph2)
end Erdos919
