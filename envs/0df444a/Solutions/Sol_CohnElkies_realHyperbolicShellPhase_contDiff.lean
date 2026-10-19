-- Prove2me | solution 1 for CohnElkies.realHyperbolicShellPhase_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/4e00191f-9044-4bb9-9cbf-6e9148f1d411

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_mellinShellPhase_analyticOnNhd

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
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (n : WithTop ℕ∞) :
    ContDiff ℝ n (realHyperbolicShellPhase ε) := by
  have hcomplex : ContDiff ℝ n (mellinShellPhase ε) :=
    ((mellinShellPhase_analyticOnNhd hε horder).restrictScalars
      (𝕜 := ℝ)).contDiff
  have harg : ContDiff ℝ n
      (fun u : ℝ => Complex.I * (u : ℂ)) := by
    exact contDiff_const.mul Complex.ofRealCLM.contDiff
  have hphase : ContDiff ℝ n
      (fun u : ℝ =>
        mellinShellPhase ε (Complex.I * (u : ℂ))) := by
    simpa only [Function.comp_apply] using! hcomplex.comp harg
  have hre : ContDiff ℝ n
      (fun u : ℝ =>
        (mellinShellPhase ε (Complex.I * (u : ℂ))).re) := by
    simpa only [Function.comp_apply] using!
      Complex.reCLM.contDiff.comp hphase
  simpa only [mellinShellPhase_imaginary, Complex.ofReal_re] using! hre
end CohnElkies
