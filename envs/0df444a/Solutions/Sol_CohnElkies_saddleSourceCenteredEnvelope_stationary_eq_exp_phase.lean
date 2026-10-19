-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredEnvelope_stationary_eq_exp_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/7c5c9f12-a5cb-4c09-bbd0-c1498b7ba36f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exp_upperGammaCenteredPhase
import Theorems.Thm_CohnElkies_saddleSourceCenteredEnvelope_eq_gamma_shell
import Theorems.Thm_CohnElkies_saddleSourceStationaryFrequencyPhase_eq
import Theorems.Thm_CohnElkies_exp_saddleSourceShellCenteredPhase

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (T : ℝ) :
    saddleSourceCenteredEnvelope ε ℓ u
        (saddleSourceStationaryLogRadius ε ℓ u) T =
      Complex.exp (saddleSourceCenteredPhase ε ℓ u T) := by
  have hη : 0 < 1 + u := by linarith
  rw [saddleSourceCenteredEnvelope_eq_gamma_shell
    hℓ hu]
  rw [saddleSourceStationaryFrequencyPhase_eq]
  unfold saddleSourceCenteredPhase
  rw [Complex.exp_add,
    exp_upperGammaCenteredPhase hℓ hη T,
    exp_saddleSourceShellCenteredPhase]
  ring
end CohnElkies
