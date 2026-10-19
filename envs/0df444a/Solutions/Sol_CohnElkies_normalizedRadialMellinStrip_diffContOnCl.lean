-- Prove2me | solution 1 for CohnElkies.normalizedRadialMellinStrip_diffContOnCl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/9ddec9b4-63c3-42ed-9a92-b747cc20f0a0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialMellinStrip_diffContOnCl

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
    (hzero : f (0 : Euclidean d) = 0) (R : ℝ) :
    DiffContOnCl ℂ (normalizedRadialMellinStrip hd f R)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hstrip := radialMellinStrip_diffContOnCl hd f hf hzero
  have hfactor :
      Differentiable ℂ
        (fun z : ℂ =>
          (radialSurfaceArea d / radialL1Mass f : ℝ) *
            Complex.exp
              (((d : ℂ) / 2 + Complex.I * z) *
                (Real.log R : ℂ))) := by
    fun_prop
  exact
    ⟨hfactor.differentiableOn.mul hstrip.differentiableOn,
      hfactor.continuous.continuousOn.mul hstrip.continuousOn⟩
end CohnElkies
