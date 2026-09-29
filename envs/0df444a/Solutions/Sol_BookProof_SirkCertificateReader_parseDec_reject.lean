-- Prove2me | solution 1 for BookProof.SirkCertificateReader.parseDec_reject
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:34:48.300984+00:00
-- url     : https://prove2.me/submissions/841e5c95-1617-4813-abc9-0ffe1217ad7e

import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader

noncomputable section

theorem solution : parseDec "NaN".toList = none := by
  rfl
