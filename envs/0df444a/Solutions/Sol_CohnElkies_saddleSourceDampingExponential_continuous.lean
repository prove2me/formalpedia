-- Prove2me | solution 1 for CohnElkies.saddleSourceDampingExponential_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/06042cca-4149-4966-9007-f272f48a0fe7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceNormalizedEnvelope_norm
import Theorems.Thm_CohnElkies_saddleSourceNormalizedEnvelope_continuous

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous
      (fun T : ℝ =>
        Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  have hnorm :=
    (saddleSourceNormalizedEnvelope_continuous
      hε hℓ hu horder).norm
  apply hnorm.congr
  intro T
  exact saddleSourceNormalizedEnvelope_norm
    hε hℓ hu horder T
end CohnElkies
