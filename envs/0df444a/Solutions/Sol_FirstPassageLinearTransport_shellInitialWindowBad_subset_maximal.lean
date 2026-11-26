-- Prove2me | solution 1 for FirstPassageLinearTransport.shellInitialWindowBad_subset_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:28.556325+00:00
-- url     : https://prove2.me/submissions/8fe6c7e1-28c5-4156-b756-03179789f705

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_orbit_envelope_of_maximalBarrier


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : 4 ≤ M) (hstart : 2 ≤ t * M) :
    shellInitialWindowBad M t ⊆
      shellMaximalParityBad M (maximalBarrierHeight t M) := by
  classical
  intro n hn
  rw [shellInitialWindowBad, Finset.mem_filter] at hn
  rw [shellMaximalParityBad, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  intro hreg
  rcases hn.2 with ⟨k, hkM, hfail⟩
  have henv := orbit_envelope_of_maximalBarrier
    ht hM hstart hkM hn.1 hreg
  rcases hfail with hlower | hupper
  · exact (not_lt_of_ge henv.1) hlower
  · exact (not_lt_of_ge henv.2) hupper
end FirstPassageLinearTransport
