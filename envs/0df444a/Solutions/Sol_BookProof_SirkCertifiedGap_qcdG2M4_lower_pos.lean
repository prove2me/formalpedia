-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.qcdG2M4_lower_pos
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:46.851641+00:00
-- url     : https://prove2.me/submissions/9d0acc72-4225-4a2b-98af-d4c8bad8b552

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.qcdG2M4_lower_pos
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution : 0 < qcdG2M4.lower := by
  norm_num [GapCertificate.lower, qcdG2M4]

#print axioms solution
