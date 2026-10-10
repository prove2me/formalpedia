-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isPhysicalFunction_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:03:21.418516+00:00
-- url     : https://prove2.me/submissions/94bec1d7-dee3-448d-ab12-3cc2336a9e71

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isPhysicalFunction_const
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}
variable {G : Type*} [Group G]


@[simp] private theorem shiftPerm_apply (m : Multiplicative ℤ) (k : ℤ) :
    shiftPerm m k = k + Multiplicative.toAdd m := rfl

set_option maxHeartbeats 1000000 in
theorem solution {d : ℤ → ℂ} (hd : IsPhysicalFunction shiftPerm d)
    (k l : ℤ) : d k = d l := by

  have h := hd (Multiplicative.ofAdd (l - k)) k
  simp only [shiftPerm_apply] at h
  rw [show k + Multiplicative.toAdd (Multiplicative.ofAdd (l - k)) = l from by
    change k + (l - k) = l; omega] at h
  exact h.symm
