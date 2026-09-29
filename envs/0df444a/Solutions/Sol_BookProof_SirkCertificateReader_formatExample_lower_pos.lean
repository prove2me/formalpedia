-- Prove2me | solution 1 for BookProof.SirkCertificateReader.formatExample_lower_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:48:27.858553+00:00
-- url     : https://prove2.me/submissions/057e4a27-8ef3-4207-a02d-1d608f8a3402

-- Generated from ChapterSirkCertificateReader.lean - theorem BookProof.SirkCertificateReader.formatExample_lower_pos
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader
open BookProof.SirkCertifiedGap

theorem solution : (0 : ℚ) < 1932 / 1000 := by
  norm_num
