-- Prove2me | solution 1 for CohnElkies.intervalIntegral_complexWallisLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/999cef93-85d9-492c-ad7c-fafe09ab07f2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexWallisLogPrimitive_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {z : ℂ} (hz : 0 < z.re) :
    (∫ s in (0 : ℝ)..1,
      Complex.log (z + (s : ℂ))) =
      (z + 1) * Complex.log (z + 1) -
        z * Complex.log z - 1 := by
  have hline : Continuous (fun s : ℝ => z + (s : ℂ)) := by
    fun_prop
  have hlog :
      ContinuousOn
        (fun s : ℝ => Complex.log (z + (s : ℂ)))
        (Set.uIcc (0 : ℝ) 1) := by
    apply hline.continuousOn.clog
    intro s hs
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hs.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      exact complexWallisLogPrimitive_hasDerivAt hz s hs)
    hlog.intervalIntegrable]
  push_cast
  simp only [add_zero]
  ring
end CohnElkies
