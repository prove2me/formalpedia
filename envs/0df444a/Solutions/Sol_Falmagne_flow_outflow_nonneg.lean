-- Prove2me | solution 1 for Falmagne.flow_outflow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:57.444089+00:00
-- url     : https://prove2.me/submissions/d87ec1cd-d8bb-4fb3-8683-65990e5b9128

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
theorem _root_.solution (h : IsFlow q m) (A : Finset X) : 0 ≤ outflow q A := by
  exact Finset.sum_nonneg fun x hx => h.nonneg x A hx
end Falmagne
