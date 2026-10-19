-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.bornPMF_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:43:14.457908+00:00
-- url     : https://prove2.me/submissions/cecdbef1-ca78-4f17-a829-131238588078

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornPMF_apply
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct


theorem solution (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ)
    (hpsi : ∑ z, ‖psi z‖ ^ 2 = 1) (z : ZMod N) :
    bornPMF v t psi hpsi z = ENNReal.ofReal (‖evolvedState v t psi z‖ ^ 2) := by
  simp [bornPMF, PMF.ofFintype_apply]

