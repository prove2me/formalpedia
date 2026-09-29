-- Prove2me | solution 1 for BookProof.SirkCertificateReader.gap_ge_of_ndjson
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:13.076192+00:00
-- url     : https://prove2.me/submissions/46cd327f-e2ee-4616-8d23-b78b0a914cbf

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.gap_ge_of_ndjson
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap




































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem solution {T P : E →ₗ[ℂ] E} {s : String} {d : CertificateData} {lo : ℚ}
    (hd : parseCertificate s = some d) (hs : ndjsonLower s = some lo)
    (hEven : sectorGround T P 1 ≤ ((d.even.theta.toQ : ℚ) : ℝ) + ((d.even.delta.toQ : ℚ) : ℝ))
    (hOdd : ((d.odd.theta.toQ : ℚ) : ℝ) - ((d.odd.delta.toQ : ℚ) : ℝ) ≤ sectorGround T P (-1)) :
    ((lo : ℚ) : ℝ) ≤ sectorGround T P (-1) - sectorGround T P 1 := by
  have hq : d.lowerQ = lo := by
    simpa only [ndjsonLower, hd, Option.map_some, Option.some.injEq] using hs
  have hv : (lo : ℝ) = (d.odd.theta.toQ : ℝ) - (d.even.theta.toQ : ℝ) -
      ((d.odd.delta.toQ : ℝ) + (d.even.delta.toQ : ℝ)) := by
    rw [← hq]
    simp only [CertificateData.lowerQ, CertificateData.gapQ, CertificateData.widthQ,
      Rat.cast_sub, Rat.cast_add]
  linarith

#print axioms solution
