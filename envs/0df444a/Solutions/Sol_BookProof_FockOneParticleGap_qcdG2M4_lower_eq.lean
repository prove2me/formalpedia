-- Prove2me | solution 1 for BookProof.FockOneParticleGap.qcdG2M4_lower_eq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:16:01.01827+00:00
-- url     : https://prove2.me/submissions/d1f0fb10-7f9f-4824-a3b3-4f396e656e52

import Definitions.Def_ChapterFockOneParticleGap
set_option autoImplicit false
theorem solution : BookProof.SirkCertifiedGap.qcdG2M4.lower = 1.932 := by
  norm_num [BookProof.SirkCertifiedGap.qcdG2M4, BookProof.SirkCertifiedGap.GapCertificate.lower]
#print axioms solution
