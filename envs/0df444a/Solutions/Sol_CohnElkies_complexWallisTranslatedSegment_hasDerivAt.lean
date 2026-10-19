-- Prove2me | solution 1 for CohnElkies.complexWallisTranslatedSegment_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/807d27db-7303-40f3-9b0c-731954663ed5

import Mathlib
import Definitions.Def_SpherePacking

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
    (z : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => z + (r : ℂ)) (1 : ℂ) s := by
  have hreal :
      HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) s := by
    simpa using! Complex.ofRealCLM.hasDerivAt
  simpa using! hreal.const_add z
end CohnElkies
