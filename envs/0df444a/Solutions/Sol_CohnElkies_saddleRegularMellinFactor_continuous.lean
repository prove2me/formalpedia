-- Prove2me | solution 1 for CohnElkies.saddleRegularMellinFactor_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/7e065547-2f66-416b-9906-6778b82cc5a6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_mellinShellPhase_continuous

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) (ℓ : ℝ) :
    Continuous (saddleRegularMellinFactor ε ℓ) := by
  have hpi : Continuous (fun z : ℂ =>
      Complex.exp
        (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2)) := by
    fun_prop
  have harg : Continuous (fun z : ℂ =>
      Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)) := by
    fun_prop
  have hphase : Continuous (fun z : ℂ =>
      Complex.exp ((ℓ : ℂ) *
        mellinShellPhase ε
          (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul
        ((mellinShellPhase_continuous hε horder).comp harg))
  exact hpi.mul hphase
end CohnElkies
