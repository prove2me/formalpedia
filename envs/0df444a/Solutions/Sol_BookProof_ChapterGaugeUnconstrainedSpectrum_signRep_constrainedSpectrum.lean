-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.signRep_constrainedSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:41:20.821223+00:00
-- url     : https://prove2.me/submissions/c20a2b14-4879-4ce9-9c18-98afc09dcf77

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.signRep_constrainedSpectrum
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_diagOp_injective
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}
variable {G : Type*} [Group G]

set_option maxHeartbeats 1000000 in
theorem solution : constrainedSpectrum signRep = {0} := by

  ext k
  simp only [constrainedSpectrum, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hk
    have hd := h (Multiplicative.ofAdd 1)
      (fun j => if j = 0 then 1 else (-1 : ℂ) ^ (1 : ℤ)) rfl
    simp only [if_neg hk] at hd
    norm_num at hd
  · rintro rfl
    intro m d hd
    have := diagOp_injective (hd ▸ rfl : diagOp
      (fun k => if k = 0 then 1 else (-1 : ℂ) ^ (Multiplicative.toAdd m)) = diagOp d)
    rw [← congrFun this 0]
    simp
