-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.sub_I_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:29.458173+00:00
-- url     : https://prove2.me/submissions/1ff5da92-90ac-4431-8939-0f73180006dd

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ} (h : z.im < 0) : z - Complex.I ≠ 0 := by
  intro hc
  have him : (z - Complex.I).im = 0 := by rw [hc, Complex.zero_im]
  simp only [Complex.sub_im, Complex.I_im] at him
  linarith
end ExponentialJuliaSetMisiurewicz
