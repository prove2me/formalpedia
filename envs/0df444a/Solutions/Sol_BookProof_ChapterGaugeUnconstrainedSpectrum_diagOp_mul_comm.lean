-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T11:48:13.379978+00:00
-- url     : https://prove2.me/submissions/8dadca77-7eef-4472-8350-4c607db86568

import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterGaugeUnconstrainedSpectrum

variable {X : Type*}

theorem solution (d e : X → ℂ) : diagOp d ∘ₗ diagOp e = diagOp e ∘ₗ diagOp d := by
  apply LinearMap.ext
  intro f
  funext x
  show d x * (e x * f x) = e x * (d x * f x)
  ring
