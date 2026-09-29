-- Prove2me | solution 1 for BookProof.SirkCertificateReader.formatExample_lower
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:13.908793+00:00
-- url     : https://prove2.me/submissions/182ebc4e-666c-4560-b7c0-d0ce793d587a

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.formatExample_lower
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap




































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem solution : ndjsonLower formatExampleNdjson = some (1932 / 1000) := by
  have hp : parseCertificate formatExampleNdjson = some formatExampleData := by
    decide
  rw [ndjsonLower, hp]
  norm_num [CertificateData.lowerQ, CertificateData.gapQ, CertificateData.widthQ,
    Decimal.toQ, formatExampleData]

#print axioms solution
