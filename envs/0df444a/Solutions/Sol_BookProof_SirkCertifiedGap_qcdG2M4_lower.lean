-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.qcdG2M4_lower
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:42.112935+00:00
-- url     : https://prove2.me/submissions/7c3bd3ac-d124-4e65-a11a-eb27b8aca619

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.qcdG2M4_lower
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution : qcdG2M4.lower = 1.932 := by
  norm_num [GapCertificate.lower, qcdG2M4]

#print axioms solution
