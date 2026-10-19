-- Prove2me | solution 1 for CohnElkies.integral_normalizedRadialLogProfile_eq_zero_of_antiFourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/399b0e14-94bd-47fc-802a-4f85d907e30e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integral_normalizedRadialLogProfile
import Theorems.Thm_CohnElkies_integral_re_eq_zero_of_antiFourier

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hradial : IsRadial g)
    (hanti : (𝓕 g : TestFunction d) = -g)
    (hzero : g (0 : Euclidean d) = 0)
    {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, normalizedRadialLogProfile hd g R v) = 0 := by
  rw [integral_normalizedRadialLogProfile hd g hradial hR,
    integral_re_eq_zero_of_antiFourier g hanti hzero]
  simp
end CohnElkies
