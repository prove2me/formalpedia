-- Prove2me | solution 1 for BookProof.SirkCertificateReader.parseDec_neg_example
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:34:13.403282+00:00
-- url     : https://prove2.me/submissions/a888bde0-d2dd-42b6-bd3c-6dfd07b68f1f

import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader

noncomputable section

theorem solution : parseDec "-0.4231".toList = some ⟨-4231, 4⟩ := by
  rfl
