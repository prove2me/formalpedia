-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.trial_at_n3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:22:06.861609+00:00
-- url     : https://prove2.me/submissions/53ccd2a0-802b-4c41-bda6-6bb170086b4b

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

theorem solution (k n : ℕ) (c : ℝ) :
    BookProof.FockCubicUnbounded.trial k n c (confAt k (n + 3)) = ((c : ℝ) : ℂ) := by
  simp [BookProof.FockCubicUnbounded.trial, Finsupp.single_apply, fk_cinj]
