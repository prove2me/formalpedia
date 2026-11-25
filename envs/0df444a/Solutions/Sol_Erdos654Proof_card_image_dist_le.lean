-- Prove2me | solution 1 for Erdos654Proof.card_image_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:52:32.462441+00:00
-- url     : https://prove2.me/submissions/1e87129a-41e7-4186-884a-35c3139f6cc1

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_xpt_zero
public import Theorems.Thm_Erdos654Proof_xpt_one
public import Theorems.Thm_Erdos654Proof_ypt_zero
public import Theorems.Thm_Erdos654Proof_ypt_one
attribute [local simp] Erdos654Proof.xpt_zero
attribute [local simp] Erdos654Proof.xpt_one
attribute [local simp] Erdos654Proof.ypt_zero
attribute [local simp] Erdos654Proof.ypt_one

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (m : ℕ) (f : Bool × ℕ → ℝ²) (x : ℝ²)
    (hf : ∀ q, dist (f q) x = dist (f (true, q.2)) x) :
    #(((idx m).image f).image fun y ↦ dist y x) ≤ m := by
  classical
  rw [image_image]
  have : (idx m).image ((fun y ↦ dist y x) ∘ f) =
      ((idx m).image Prod.snd).image fun j ↦ dist (f (true, j)) x := by
    rw [image_image]
    exact image_congr fun q _ ↦ hf q
  rw [this]
  refine card_image_le.trans ((card_le_card ?_).trans (card_range m).le)
  intro j hj
  simp only [idx, mem_image, mem_product, mem_univ, true_and] at hj
  obtain ⟨⟨_, k⟩, hk, rfl⟩ := hj
  exact hk
end Erdos654Proof
