-- Prove2me | solution 1 for BookProof.SirkCertificateReader.Decimal.toQ_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:27:27.840756+00:00
-- url     : https://prove2.me/submissions/5d78734e-7eef-4361-9d78-25b739686ffd

import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader
open BookProof.SirkCertificateReader.Decimal

theorem solution {d : Decimal} (h : 0 ≤ d.mant) : 0 ≤ d.toQ := by
  unfold Decimal.toQ
  positivity
