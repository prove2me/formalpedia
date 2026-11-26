-- Prove2me | solution 1 for Falmagne.flow_inflow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:50.225697+00:00
-- url     : https://prove2.me/submissions/ad2a141f-8c53-43d2-9171-ccc727af068f

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}
namespace Falmagne
theorem _root_.solution (h : IsFlow q m) (A : Finset X) : 0 ≤ inflow q A := by
  apply Finset.sum_nonneg
  intro y hy
  exact h.nonneg y (insert y A) (Finset.mem_insert_self _ _)
end Falmagne
