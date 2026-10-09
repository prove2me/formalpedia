-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.shift_full_spectrum_vs_observable_spectrum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:41:22.809982+00:00
-- url     : https://prove2.me/submissions/3d9b13d2-70bd-47e7-a140-a70d9756c8c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.shift_full_spectrum_vs_observable_spectrum
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_constrainedSpectrum_eq_univ_of_isUnconstrained
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_shift_isUnconstrainedGaugeFixing
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_shift_observableSpectrum_subsingleton
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}
variable {G : Type*} [Group G]

set_option maxHeartbeats 1000000 in
theorem solution :
    IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) ∧
      constrainedSpectrum (fun m : Multiplicative ℤ => permOp (shiftPerm m)) =
        (Set.univ : Set ℤ) ∧
      (Set.univ : Set ℤ).Infinite ∧
      Subsingleton (observableSpectrum shiftPerm) := by

  refine ⟨shift_isUnconstrainedGaugeFixing, ?_, Set.infinite_univ,
    shift_observableSpectrum_subsingleton⟩
  refine constrainedSpectrum_eq_univ_of_isUnconstrained shift_isUnconstrainedGaugeFixing ?_
  ext f k
  change f ((shiftPerm 1).symm k) = f k
  have h1 : shiftPerm 1 = (1 : Equiv.Perm ℤ) := by ext k; simp
  rw [h1]
  simp [Equiv.Perm.one_def]
