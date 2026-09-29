-- Prove2me | solution 1 for BookProof.SirkCertificateReader.formatExample_width
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:14.63655+00:00
-- url     : https://prove2.me/submissions/d4485d2b-0121-4c80-9ee4-167a9bb1575b

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.formatExample_width
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap




































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem solution : formatExampleData.widthQ = 555 / 10000 := by
  norm_num [CertificateData.widthQ, Decimal.toQ, formatExampleData]

#print axioms solution
