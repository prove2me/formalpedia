-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/b74999e3-b774-4336-ae77-6070eb4b0fa4

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
theorem _root_.solution (x : ℝ) :
    HasDerivAt upperImaginaryExp
      (Complex.I * upperImaginaryExp x) x := by
  have hreal :
      HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
    simpa using! Complex.ofRealCLM.hasDerivAt
  have hlinear :
      HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ))
        Complex.I x := by
    convert! hreal.const_mul Complex.I using 1
    all_goals simp
  convert! hlinear.cexp using 1
  all_goals simp [upperImaginaryExp, mul_comm]
end CohnElkies
