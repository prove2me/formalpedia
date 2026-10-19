-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/9ec8a84a-1c27-4d9f-a3e6-c4d357e204b0

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ContDiff ℝ (⊤ : WithTop ℕ∞) upperImaginaryExp := by
  unfold upperImaginaryExp
  have hreal :
      ContDiff ℝ (⊤ : WithTop ℕ∞)
        (fun x : ℝ => (x : ℂ)) :=
    Complex.ofRealCLM.contDiff
  exact (contDiff_const.mul hreal).cexp
end CohnElkies
