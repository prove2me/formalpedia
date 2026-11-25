-- Prove2me | solution 1 for Erdos657.erdos_657.variants.straus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:18:05.631793+00:00
-- url     : https://prove2.me/submissions/6358bc4a-26c7-475f-bfb3-1b0960f75966

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
public import Theorems.Thm_Erdos657Proof_straus

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657
namespace Erdos657
namespace erdos_657.variants
theorem _root_.solution (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 :=
  Erdos657Proof.straus k
end erdos_657.variants
end Erdos657
