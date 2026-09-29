-- Prove2me | solution 1 for BookProof.SirkCertificateReader.toGapCertificate_lower
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:17.033784+00:00
-- url     : https://prove2.me/submissions/2d4c23aa-4d25-4224-81c6-2328f993646a

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.toGapCertificate_lower
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem solution {d : CertificateData} {c : GapCertificate}
    (h : d.toGapCertificate = some c) : c.lower = ((d.lowerQ : ℚ) : ℝ) := by
  unfold CertificateData.toGapCertificate at h
  split_ifs at h with hw
  · have hc := Option.some.inj h
    subst c
    simp only [GapCertificate.lower, CertificateData.lowerQ, Rat.cast_sub]

#print axioms solution
