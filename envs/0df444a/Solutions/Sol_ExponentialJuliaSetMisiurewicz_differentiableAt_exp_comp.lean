-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.differentiableAt_exp_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:44.766533+00:00
-- url     : https://prove2.me/submissions/509697a1-c415-4b37-b00f-6c8471c883f4

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

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (fun w => Complex.exp (f w)) z := by
  exact Complex.differentiableAt_exp.comp z hf
end ExponentialJuliaSetMisiurewicz
