-- Prove2me | solution 1 for BookProof.SirkCertificateReader.parseDec_int_example
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:49:49.063546+00:00
-- url     : https://prove2.me/submissions/e03976e4-bc94-452d-a43c-247aacc0c5ab

import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader

noncomputable section

theorem solution : parseDec "7".toList = some ⟨7, 0⟩ := by
  rfl
