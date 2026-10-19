-- Prove2me | solution 1 for CohnElkies.complexShellInterval_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/24e0ce60-a861-4c1e-b097-2216cc0f4b3b

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun z : ℂ =>
      ∫ x in a..b,
        (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) := by
  let F : ℂ → ℝ → ℂ := fun z x =>
    (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)
  have hF : Continuous (Function.uncurry F) := by
    try dsimp [F, Function.uncurry]
    exact (Complex.continuous_ofReal.comp
      (hw.comp continuous_snd)).mul (by fun_prop)
  have hparam : Continuous
      (fun z : ℂ => ∫ x in Set.Icc a b, F z x) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) hF isCompact_Icc
  have hident (z : ℂ) :
      (∫ x in a..b,
        (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) =
        (∫ x in Set.Icc a b, F z x) := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  exact hparam.congr (fun z => (hident z).symm)
end CohnElkies
