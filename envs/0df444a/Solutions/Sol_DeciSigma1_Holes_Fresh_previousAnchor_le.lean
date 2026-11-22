-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.previousAnchor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:45:17.491287+00:00
-- url     : https://prove2.me/submissions/1374860d-6317-4d50-ab67-bbf80cb97487

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
theorem _root_.solution {p s : ℕ} (h : ∀ q ∈ A, q < p → q ≤ s) : previousAnchor A p ≤ s :=
  Finset.sup_le fun q hq => h q (mem_filter.mp hq).1 (mem_filter.mp hq).2
end DeciSigma1.Holes.Fresh
