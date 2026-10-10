-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.shiftPerm_movesEveryPoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:03:09.445114+00:00
-- url     : https://prove2.me/submissions/7ef2226b-188a-43be-92fd-9250807ff3fb

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.shiftPerm_movesEveryPoint
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}
variable {G : Type*} [Group G]


@[simp] private theorem shiftPerm_apply (m : Multiplicative ℤ) (k : ℤ) :
    shiftPerm m k = k + Multiplicative.toAdd m := rfl

set_option maxHeartbeats 1000000 in
theorem solution (m : Multiplicative ℤ) (hm : m ≠ 1) (k : ℤ) :
    shiftPerm m k ≠ k := by

  have hm' : Multiplicative.toAdd m ≠ 0 := fun h => hm (by
    apply Multiplicative.toAdd.injective
    simpa using h)
  simp only [shiftPerm_apply]
  omega
