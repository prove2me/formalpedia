-- Prove2me | solution 1 for DinitzGargGoemans.strictDggRoundingImpWeak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:54:21.478245+00:00
-- url     : https://prove2.me/submissions/8c7f9190-6bea-44dd-99d2-f23ab9298a07

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution
    [Fintype Commodity] [Fintype RouteChoice] [Fintype Arc]
    [Nonempty Commodity]
    {I : PathFlowInstance Commodity RouteChoice Arc}
    {f : Commodity → RouteChoice → ℚ}
    {q : Commodity → RouteChoice}
    (h : strictDggRounding I f q) : weakDggRounding I f q := by
  rcases h with ⟨routing, bound, cost⟩
  exact ⟨routing, fun a => (bound a).le, cost⟩
end DinitzGargGoemans
