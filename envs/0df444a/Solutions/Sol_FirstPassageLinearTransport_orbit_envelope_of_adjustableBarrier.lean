-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_envelope_of_adjustableBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:55.828795+00:00
-- url     : https://prove2.me/submissions/c3d798b7-2b3d-461a-a8d7-91eaab292925

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Theorems.Thm_FirstPassageLinearTransport_orbit_envelope_of_regularBarrier
import Theorems.Thm_FirstPassageLinearTransport_adjustableBarrier_phase
import Theorems.Thm_FirstPassageLinearTransport_adjustableBarrier_phase_two
import Theorems.Thm_FirstPassageLinearTransport_adjustableBarrier_correction_absorb

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} {M n k : ℕ}
    (hlambda1 : lambda ≤ 1) (ht : 0 ≤ t)
    (hmainStartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hcorrectionStartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ)))
    (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hreg :
      MaximalParityRegular n M (adjustableBarrierHeight lambda t M)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  exact orbit_envelope_of_regularBarrier hkM hnShell hreg
    (adjustableBarrier_phase hlambda1 ht hnShell)
    (adjustableBarrier_phase_two ht hmainStartup hnShell)
    (adjustableBarrier_correction_absorb ht hkM hnShell hcorrectionStartup)
end FirstPassageLinearTransport
