-- Prove2me | solution 1 for Falmagne.flow_edge_le_outflow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:58.972018+00:00
-- url     : https://prove2.me/submissions/0f97b064-8569-4bd1-8b04-b9f219e202ba

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
theorem _root_.solution (h : IsFlow q m) (hx : x ∈ A) : q x A ≤ outflow q A := by
  exact Finset.single_le_sum (fun y hy => h.nonneg y A hy) hx
end Falmagne
