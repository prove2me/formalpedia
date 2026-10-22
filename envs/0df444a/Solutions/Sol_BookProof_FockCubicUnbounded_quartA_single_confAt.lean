-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.quartA_single_confAt
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:22:12.303905+00:00
-- url     : https://prove2.me/submissions/2c86335d-799f-4859-a93f-393f82db7b04

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

theorem solution (k m : ℕ) (z : ℂ) :
    quartA k (Finsupp.single (confAt k m) z)
      = Finsupp.single (confAt k m) ((((m : ℝ) * ((m : ℝ) - 1) : ℝ) : ℂ) * z) := by
  simp only [quartA, LinearMap.comp_apply, fk_annA, fk_creA]
  rcases m with _ | _ | m
  · simp [confAt, dn, up]
  · simp [confAt, dn, up]
  · have e1 : dn k (confAt k (m + 2)) = confAt k (m + 1) := by
      ext j; simp only [confAt, dn, up, Finsupp.update_apply, Finsupp.single_apply]; split_ifs <;> omega
    have e2 : dn k (confAt k (m + 1)) = confAt k m := by
      ext j; simp only [confAt, dn, up, Finsupp.update_apply, Finsupp.single_apply]; split_ifs <;> omega
    have e3 : up k (confAt k m) = confAt k (m + 1) := by
      ext j; simp only [confAt, dn, up, Finsupp.update_apply, Finsupp.single_apply]; split_ifs <;> omega
    have e4 : up k (confAt k (m + 1)) = confAt k (m + 2) := by
      ext j; simp only [confAt, dn, up, Finsupp.update_apply, Finsupp.single_apply]; split_ifs <;> omega
    have ev : ∀ j, (confAt k j) k = j := fun j => by simp [confAt]
    rw [e1, ev, e2, ev, e3, ev, e4, ev]
    congr 1
    have h1 : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have h2 : Real.sqrt ((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2) = (m : ℝ) + 2 :=
      Real.mul_self_sqrt (by positivity)
    have hA : ((Real.sqrt ((m:ℝ) + 2) : ℝ) : ℂ) * ((Real.sqrt ((m:ℝ) + 2) : ℝ) : ℂ) = (m:ℂ) + 2 := by
      rw [← Complex.ofReal_mul, h2]; push_cast; ring
    have hB : ((Real.sqrt ((m:ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((m:ℝ) + 1) : ℝ) : ℂ) = (m:ℂ) + 1 := by
      rw [← Complex.ofReal_mul, h1]; push_cast; ring
    push_cast
    simp only [show (m:ℝ) + 1 + 1 = (m:ℝ) + 2 by ring]
    linear_combination z * ((Real.sqrt ((m:ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((m:ℝ) + 1) : ℝ) : ℂ) * hA
      + z * ((m:ℂ) + 2) * hB
