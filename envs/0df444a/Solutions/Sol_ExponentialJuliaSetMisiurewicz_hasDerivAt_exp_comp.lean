-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.hasDerivAt_exp_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:25.035329+00:00
-- url     : https://prove2.me/submissions/129f59d2-f70e-4257-84ad-275f6a20166f

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (Complex.exp ∘ f)
      (f' * Complex.exp (f z)) z := by
  simpa [mul_comm] using
    (Complex.hasDerivAt_exp (f z)).comp z hf
end ExponentialJuliaSetMisiurewicz
