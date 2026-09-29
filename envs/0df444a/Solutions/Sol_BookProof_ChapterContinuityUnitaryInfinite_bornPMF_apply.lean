-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitaryInfinite.bornPMF_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T05:05:54.705754+00:00
-- url     : https://prove2.me/submissions/eacb42db-3f39-4359-bb2b-24cd782724d6

-- Generated from ChapterContinuityUnitaryInfinite.lean — solution of BookProof.ChapterContinuityUnitaryInfinite.bornPMF_apply
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite








open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (v : LinfZ) (t : ℝ) (psi : L2Z) (hpsi : ‖psi‖ = 1) (z : ℤ) :
    bornPMF v t psi hpsi z
      = ENNReal.ofReal (‖((evolvedState v t psi : L2Z) : ℤ → ℂ) z‖ ^ 2) := rfl
