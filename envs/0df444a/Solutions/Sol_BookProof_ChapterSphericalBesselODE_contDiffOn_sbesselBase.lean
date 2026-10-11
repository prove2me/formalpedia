-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.contDiffOn_sbesselBase
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:36.685305+00:00
-- url     : https://prove2.me/submissions/61808896-1693-4234-a115-8bd6dae485e0

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.contDiffOn_sbesselBase
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution : ContDiffOn ℝ (⊤ : ℕ∞) sbesselBase {r : ℝ | r ≠ 0} := by

  apply ContDiffOn.div Real.contDiff_sin.contDiffOn contDiff_id.contDiffOn
  intro x hx; exact hx
