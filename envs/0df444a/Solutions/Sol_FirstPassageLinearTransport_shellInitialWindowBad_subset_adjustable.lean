-- Prove2me | solution 1 for FirstPassageLinearTransport.shellInitialWindowBad_subset_adjustable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:00.388592+00:00
-- url     : https://prove2.me/submissions/e4e6c3ef-63eb-4ec2-beaa-ae93ad922416

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_orbit_envelope_of_adjustableBarrier


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} {M : ℕ}
    (hlambda1 : lambda ≤ 1) (ht : 0 ≤ t)
    (hmainStartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hcorrectionStartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    shellInitialWindowBad M t ⊆
      shellMaximalParityBad M (adjustableBarrierHeight lambda t M) := by
  classical
  intro n hn
  rw [shellInitialWindowBad, Finset.mem_filter] at hn
  rw [shellMaximalParityBad, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  intro hreg
  rcases hn.2 with ⟨k, hkM, hfail⟩
  have henv := orbit_envelope_of_adjustableBarrier hlambda1 ht
    hmainStartup hcorrectionStartup hkM hn.1 hreg
  rcases hfail with hlower | hupper
  · exact (not_lt_of_ge henv.1) hlower
  · exact (not_lt_of_ge henv.2) hupper
end FirstPassageLinearTransport
