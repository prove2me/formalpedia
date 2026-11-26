-- Prove2me | solution 1 for FriedCrossing.Scale.one_le_lossBudget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:05:19.3948+00:00
-- url     : https://prove2.me/submissions/01932d55-ac5d-4c69-ab2a-1d02cc2ddc20

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution (k : ℕ) : 1 ≤ lossBudget k := by
  induction k with
  | zero => simp [lossBudget]
  | succ k ih => simp only [lossBudget]; omega
end FriedCrossing.Scale
