-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.le_previousAnchor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:34.117429+00:00
-- url     : https://prove2.me/submissions/6aea2f46-2b79-41d4-938a-2beba661cfbd

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {A : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {p q : ℕ} (hq : q ∈ A) (hqp : q < p) : q ≤ previousAnchor A p :=
  le_sup (f := id) (mem_filter.mpr ⟨hq, hqp⟩)
end DeciSigma1.Holes.Fresh
