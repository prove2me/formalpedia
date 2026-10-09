-- Prove2me | solution 1 for BookProof.ChapterGaugeComprehensiveFixing.shift_movesEveryPointOfSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:29:18.7044+00:00
-- url     : https://prove2.me/submissions/c4dfafbb-94a3-4890-9d6d-236e4c5db7fc

-- Generated from ChapterGaugeComprehensiveFixing.lean — solution of BookProof.ChapterGaugeComprehensiveFixing.shift_movesEveryPointOfSpectrum
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
import Theorems.Thm_BookProof_ChapterGaugeComprehensiveFixing_shift_smul_def
open BookProof.ChapterGaugeComprehensiveFixing




open BookProof.ChapterGaugeIncompleteFixing

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G] [MulAction G X]
variable (X : Type*) (G : Type*) [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution :
    MovesEveryPointOfSpectrum (Multiplicative ℤ) ℝ := by

  intro g hg x hx
  rw [shift_smul_def] at hx
  apply hg
  have h0 : ((Multiplicative.toAdd g : ℤ) : ℝ) = 0 := by linarith
  have : (Multiplicative.toAdd g : ℤ) = 0 := by exact_mod_cast h0
  exact Multiplicative.toAdd.injective this
