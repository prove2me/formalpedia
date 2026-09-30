-- Prove2me | solution 2 for BookProof.SirkGapTable.CouplingCertificate.lo_le_hi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T20:00:03.119835+00:00
-- url     : https://prove2.me/submissions/207fcab9-e3ce-4af8-8493-3c2facff2917

-- Generated from ChapterSirkGapTable.lean — solution of BookProof.SirkGapTable.CouplingCertificate.lo_le_hi
import Mathlib
import Definitions.Def_ChapterSirkGapTable
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkGapTable










noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (c : CouplingCertificate) : c.lo ≤ c.hi := by

  have := c.width_nonneg
  simp only [CouplingCertificate.lo, CouplingCertificate.hi]
  linarith
