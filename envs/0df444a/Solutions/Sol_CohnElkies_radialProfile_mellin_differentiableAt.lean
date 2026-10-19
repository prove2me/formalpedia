-- Prove2me | solution 1 for CohnElkies.radialProfile_mellin_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/ad730369-e981-4de3-a83c-b2c8264778d7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_isBigO_rpow_two_zero
import Theorems.Thm_CohnElkies_radialProfile_isBigO_rpow_atTop
import Theorems.Thm_CohnElkies_radialProfile_locallyIntegrableOn

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (s : ℂ) (hs : -2 < s.re) :
    DifferentiableAt ℂ (mellin (radialProfile hd f)) s := by
  apply mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := (-2 : ℝ))
    (radialProfile_locallyIntegrableOn hd f)
    (radialProfile_isBigO_rpow_atTop hd f (s.re + 1))
    (by linarith)
  · simpa using! radialProfile_isBigO_rpow_two_zero hd f hf hzero
  · exact hs
end CohnElkies
