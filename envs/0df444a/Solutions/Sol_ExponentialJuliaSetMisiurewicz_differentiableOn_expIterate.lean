-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.differentiableOn_expIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:05.391673+00:00
-- url     : https://prove2.me/submissions/d32d2910-b5e9-40bd-88f1-7d777792b302

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Definitions.Def_ExpChaotic_Basic
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiable_expIterate

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution (n : ℕ) (s : Set ℂ) :
    DifferentiableOn ℂ (expIterate n) s :=
  (differentiable_expIterate n).differentiableOn
end ExponentialJuliaSetMisiurewicz
