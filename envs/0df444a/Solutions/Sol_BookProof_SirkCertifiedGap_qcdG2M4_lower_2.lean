-- Prove2me | solution 2 for BookProof.SirkCertifiedGap.qcdG2M4_lower
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T19:31:39.448206+00:00
-- url     : https://prove2.me/submissions/51af2f91-9590-41e3-b362-dc472aa75d53

-- Generated from ChapterSirkCertifiedGap.lean — solution of BookProof.SirkCertifiedGap.qcdG2M4_lower
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap











noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution : qcdG2M4.lower = 1.932 := by

  norm_num [GapCertificate.lower, qcdG2M4]
