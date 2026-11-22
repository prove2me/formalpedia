-- Prove2me | solution 1 for GJKKL.greedyKernel_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:49.704962+00:00
-- url     : https://prove2.me/submissions/e61dcc52-a3fe-4aca-be25-cb309c40d799

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) (a : Finset V) :
    (greedyKernel H).K h a = if a ∈ avail H h then ((avail H h).card : ℝ)⁻¹ else 0 := rfl
end GJKKL
