-- Prove2me | solution 1 for BookProof.SirkCertificateReader.formatExample_gap
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:12.216571+00:00
-- url     : https://prove2.me/submissions/5dc34eae-0f60-4555-8fa2-0f919a239c21

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.formatExample_gap
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap




































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem solution : formatExampleData.gapQ = 19875 / 10000 := by
  norm_num [CertificateData.gapQ, Decimal.toQ, formatExampleData]

#print axioms solution
