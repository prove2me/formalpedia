-- Prove2me | solution 1 for Erdos654.erdos_654.variants.feng
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:48:23.511528+00:00
-- url     : https://prove2.me/submissions/80dd6eba-64a4-4252-8ce4-a969c91a2748

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_feng

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654
namespace Erdos654
namespace erdos_654.variants
theorem _root_.solution (m : ℕ) (hm : 10 ≤ m) :
    ∃ A : Finset ℝ², #A = 4 * m ∧ NoFourConcyclic A ∧
      ∀ x ∈ A, distinctDistancesFrom A x < 3 * m :=
  Erdos654Proof.feng m (by omega)
end erdos_654.variants
end Erdos654
