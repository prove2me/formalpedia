-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.trial_at_other
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T03:22:08.290064+00:00
-- url     : https://prove2.me/submissions/7b0ffb81-3446-4bd1-acdd-ab15ee0736f8

import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterTempleSeparationNecessary
open BookProof.FockSecondQuantization
open BookProof.TempleSeparationNecessary
open BookProof.FockCubicUnbounded

noncomputable section

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

theorem fk_cinj (k m n : ℕ) : confAt k m = confAt k n ↔ m = n := by
  unfold confAt
  rw [Finsupp.single_eq_single_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, h2⟩)
    · exact h
    · rw [h1, h2]
  · intro h; exact Or.inl ⟨rfl, h⟩

theorem fk_annA (j : ℕ) (β : Conf) (z : ℂ) :
    annA j (Finsupp.single β z) = Finsupp.single (dn j β) (z * ((Real.sqrt (β j) : ℝ) : ℂ)) := by
  simp [annA, Finsupp.smul_single]

theorem fk_creA (j : ℕ) (β : Conf) (z : ℂ) :
    creA j (Finsupp.single β z) =
      Finsupp.single (up j β) (z * ((Real.sqrt ((β j : ℝ) + 1) : ℝ) : ℂ)) := by
  simp [creA, Finsupp.smul_single]

theorem solution {k n : ℕ} {c : ℝ} {m : ℕ} (h1 : m ≠ n) (h2 : m ≠ n + 3) :
    BookProof.FockCubicUnbounded.trial k n c (confAt k m) = 0 := by
  simp [BookProof.FockCubicUnbounded.trial, Finsupp.single_apply, fk_cinj, Ne.symm h1, Ne.symm h2]
