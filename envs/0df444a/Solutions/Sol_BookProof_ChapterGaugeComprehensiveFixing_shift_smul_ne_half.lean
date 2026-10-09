-- Prove2me | solution 1 for BookProof.ChapterGaugeComprehensiveFixing.shift_smul_ne_half
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:29:32.937505+00:00
-- url     : https://prove2.me/submissions/e4b2ac92-7a6e-432a-a9f9-d5171d8c21ee

-- Generated from ChapterGaugeComprehensiveFixing.lean — solution of BookProof.ChapterGaugeComprehensiveFixing.shift_smul_ne_half
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
theorem solution {s : ℝ} (hs : s = 0 ∨ s = 1) (g : Multiplicative ℤ) :
    g • s ≠ (1 / 2 : ℝ) := by

  rw [shift_smul_def]
  intro hcontra
  have hz : ((2 * Multiplicative.toAdd g : ℤ) : ℝ) = ((1 : ℤ) : ℝ) ∨
      ((2 * Multiplicative.toAdd g : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by
    rcases hs with hs | hs <;> subst hs <;> push_cast <;> [left; right] <;> linarith
  have hz' : 2 * Multiplicative.toAdd g = 1 ∨ 2 * Multiplicative.toAdd g = -1 := by
    rcases hz with hz | hz
    · exact Or.inl (by exact_mod_cast hz)
    · exact Or.inr (by exact_mod_cast hz)
  omega
