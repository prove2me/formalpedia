-- Prove2me | solution 1 for BookProof.SirkCertificateReader.parseDec_example
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:34:17.962739+00:00
-- url     : https://prove2.me/submissions/153c86ca-5265-4d57-a8d8-1a904eac9e5d

import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader

noncomputable section

theorem solution : parseDec "1.9875".toList = some ⟨19875, 4⟩ := by
  rfl
