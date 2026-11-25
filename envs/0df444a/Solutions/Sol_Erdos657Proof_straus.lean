-- Prove2me | solution 1 for Erdos657Proof.straus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:11:00.811187+00:00
-- url     : https://prove2.me/submissions/6aeec52b-386a-4621-9877-67e90add7366

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
public import Theorems.Thm_Erdos657Proof_card_A
public import Theorems.Thm_Erdos657Proof_isIsoscelesFree_A
public import Theorems.Thm_Erdos657Proof_distinctDistances_A

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset
namespace Erdos657Proof
theorem _root_.solution (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 :=
  ⟨univ.image pt, card_A k, isIsoscelesFree_A k, distinctDistances_A k⟩
end Erdos657Proof
