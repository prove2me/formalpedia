-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.trial_quartic_form
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T03:23:08.863182+00:00
-- url     : https://prove2.me/submissions/c6b70ecf-6460-4092-b62f-72747d6d66e4

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

theorem fk_quart (k m : ℕ) (z : ℂ) :
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

theorem fk_toLp (u : FockAlg) (α : Conf) : (toLp u : Conf → ℂ) α = u α := rfl

theorem solution (k n : ℕ) (c : ℝ) :
    (inner ℂ (toLp (BookProof.FockCubicUnbounded.trial k n c))
      (toLp (quartA k (BookProof.FockCubicUnbounded.trial k n c))) : ℂ).re
      = (n : ℝ) * ((n : ℝ) - 1) + ((n : ℝ) + 3) * ((n : ℝ) + 2) * c ^ 2 := by
  set a := confAt k n
  set b := confAt k (n + 3)
  have hab : a ≠ b := by
    intro h; have := (fk_cinj k n (n + 3)).mp h; omega
  have hq : quartA k (BookProof.FockCubicUnbounded.trial k n c) =
      Finsupp.single a ((((n : ℝ) * ((n : ℝ) - 1) : ℝ) : ℂ) * 1) +
      Finsupp.single b (((((n + 3 : ℕ) : ℝ) * (((n + 3 : ℕ) : ℝ) - 1) : ℝ) : ℂ) * ((c : ℝ) : ℂ)) := by
    rw [BookProof.FockCubicUnbounded.trial, map_add, fk_quart, fk_quart]
  rw [hq, lp.inner_eq_tsum]
  have hsupp : ∀ α ∉ ({a, b} : Finset Conf),
      inner ℂ ((toLp (BookProof.FockCubicUnbounded.trial k n c) : Conf → ℂ) α)
        ((toLp (Finsupp.single a ((((n : ℝ) * ((n : ℝ) - 1) : ℝ) : ℂ) * 1) +
          Finsupp.single b (((((n + 3 : ℕ) : ℝ) * (((n + 3 : ℕ) : ℝ) - 1) : ℝ) : ℂ) *
            ((c : ℝ) : ℂ))) : Conf → ℂ) α) = 0 := by
    intro α hα
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    show inner ℂ ((BookProof.FockCubicUnbounded.trial k n c) α) _ = 0
    simp [BookProof.FockCubicUnbounded.trial, Finsupp.single_apply, Ne.symm hα.1, Ne.symm hα.2, a, b]
  rw [tsum_eq_sum hsupp, Finset.sum_pair hab]
  simp only [fk_toLp]
  have ta : (BookProof.FockCubicUnbounded.trial k n c) a = 1 := by
    simp [BookProof.FockCubicUnbounded.trial, Finsupp.single_apply, fk_cinj, a]
  have tb : (BookProof.FockCubicUnbounded.trial k n c) b = ((c : ℝ) : ℂ) := by
    simp [BookProof.FockCubicUnbounded.trial, Finsupp.single_apply, fk_cinj, b]
  rw [ta, tb]
  simp only [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl, if_neg hab, if_neg (Ne.symm hab)]
  simp [Complex.inner, RCLike.inner_apply]
  push_cast
  ring
