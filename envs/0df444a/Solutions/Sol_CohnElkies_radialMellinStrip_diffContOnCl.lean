-- Prove2me | solution 1 for CohnElkies.radialMellinStrip_diffContOnCl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/5d4cc643-fc6f-4d82-b1ce-21beb012499b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialMellinStrip_differentiableAt

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
    (hzero : f (0 : Euclidean d) = 0) :
    DiffContOnCl ℂ (radialMellinStrip hd f)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hhalf : 0 < (d : ℝ) / 2 := by
    exact half_pos (Nat.cast_pos.mpr hd)
  apply DifferentiableOn.diffContOnCl
  intro z hz
  rw [Complex.closure_preimage_im,
    closure_Ioo (ne_of_lt (neg_lt_self hhalf))] at hz
  apply
    (radialMellinStrip_differentiableAt
      hd f hf hzero z (by linarith [hz.1])).differentiableWithinAt
end CohnElkies
