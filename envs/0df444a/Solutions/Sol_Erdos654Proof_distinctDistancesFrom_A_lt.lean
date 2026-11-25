-- Prove2me | solution 1 for Erdos654Proof.distinctDistancesFrom_A_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:05:02.01389+00:00
-- url     : https://prove2.me/submissions/b6e474eb-753a-4f27-91f4-5c6db5b1814f

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_card_XS
public import Theorems.Thm_Erdos654Proof_card_YS
public import Theorems.Thm_Erdos654Proof_distinctDistancesFrom_union_le
public import Theorems.Thm_Erdos654Proof_card_image_dist_le
public import Theorems.Thm_Erdos654Proof_dist_ypt
public import Theorems.Thm_Erdos654Proof_dist_xpt

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (m : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ A m, distinctDistancesFrom (A m) x < 3 * m := by
  intro x hx
  rcases mem_union.1 hx with hX | hY
  · obtain ⟨p, -, rfl⟩ := mem_image.1 hX
    have h1 := distinctDistancesFrom_union_le (XS m) (YS m) hX
    have h2 := card_image_dist_le m ypt (xpt p) (fun q ↦ dist_ypt p q)
    rw [card_XS] at h1
    rw [A]
    change _ ≤ _ + #(((idx m).image ypt).image _) at h1
    omega
  · obtain ⟨p, -, rfl⟩ := mem_image.1 hY
    have h1 := distinctDistancesFrom_union_le (YS m) (XS m) hY
    have h2 := card_image_dist_le m xpt (ypt p) (fun q ↦ dist_xpt p q)
    rw [card_YS] at h1
    rw [A, union_comm]
    change _ ≤ _ + #(((idx m).image xpt).image _) at h1
    omega
end Erdos654Proof
