-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.shift_observableSpectrum_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T12:10:18.045532+00:00
-- url     : https://prove2.me/submissions/c137ea61-509c-47aa-8269-3f1734486542

import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum

theorem solution : Subsingleton (observableSpectrum shiftPerm) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with
  | h x =>
  induction b using Quotient.inductionOn with
  | h y =>
  apply Quotient.sound
  refine ⟨Multiplicative.ofAdd (y - x), ?_⟩
  show x + Multiplicative.toAdd (Multiplicative.ofAdd (y - x)) = y
  simp
