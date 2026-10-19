-- Prove2me | solution 2 for BookProof.ChapterReconstruct.offDiag_unit_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:21:55.352838+00:00
-- url     : https://prove2.me/submissions/32a83457-5284-4ed6-86f9-5a9e3c9f967b

import Mathlib
import Definitions.Def_ChapterReconstruct
-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.offDiag_unit_iff
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}
theorem h44_offDiag_two {n : ℕ} (U : Fin n → Fin n → ℂ) (a l m : Fin n) (hlm : l ≠ m) (r c : ℂ) :
    BookProof.ChapterReconstruct.offDiag U a
      (fun k => if k = l then r else if k = m then r * c else 0) =
      (starRingEnd ℂ) (U l a) * r * (starRingEnd ℂ) (r * c) * U m a +
      (starRingEnd ℂ) (U m a) * (r * c) * (starRingEnd ℂ) r * U l a := by
  unfold BookProof.ChapterReconstruct.offDiag
  have hml : m ≠ l := Ne.symm hlm
  rw [Fintype.sum_eq_add l m hlm]
  · rw [Fintype.sum_eq_add l m hlm, Fintype.sum_eq_add l m hlm]
    · simp [hlm, hml]
    · intro x hx; simp [hx.1, hx.2]
    · intro x hx; simp [hx.1, hx.2]
  · intro x hx
    apply Finset.sum_eq_zero
    intro b _
    simp [hx.1, hx.2]

theorem solution (U : Fin n → Fin n → ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 →
        offDiag U a Ψ = 0) ↔ IsDeterministic U := by
  constructor
  · intro h a l m hlm
    have r2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow]; simp
    set r : ℂ := ((Real.sqrt (1/2) : ℝ) : ℂ) with hr
    have hrr : (starRingEnd ℂ) r = r := Complex.conj_ofReal _
    have hr2 : r * r = 1/2 := by
      rw [hr, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
    have hnorm : ∀ c : ℂ, ‖c‖ = 1 →
        (∑ k : Fin n, ‖(fun k => if k = l then r else if k = m then r * c else 0) k‖ ^ 2) = 1 := by
      intro c hc
      have hml : m ≠ l := Ne.symm hlm
      rw [Fintype.sum_eq_add l m hlm]
      · have : ‖r‖ ^ 2 = 1/2 := by
          have := congrArg (fun z : ℂ => ‖z‖) hr2
          simp only [norm_mul] at this
          rw [sq, this]; simp
        simp only [if_true, if_neg hml, norm_mul, hc, mul_one, this]
        norm_num
      · intro x hx; simp [hx.1, hx.2]
    have h1 := h a _ (hnorm 1 (by simp))
    have h2 := h a _ (hnorm Complex.I (by simp))
    rw [h44_offDiag_two U a l m hlm] at h1 h2
    simp only [map_mul, map_one, Complex.conj_I, hrr] at h1 h2
    have hz : (starRingEnd ℂ) (U l a) * U m a = (starRingEnd ℂ) ((starRingEnd ℂ) (U m a) * U l a) := by
      simp [mul_comm]
    set z := (starRingEnd ℂ) (U m a) * U l a with hzdef
    have e1 : (r * r) * ((starRingEnd ℂ) z + z) = 0 := by
      rw [← hz]; linear_combination h1
    have e2 : (r * r) * Complex.I * (z - (starRingEnd ℂ) z) = 0 := by
      rw [← hz]; linear_combination h2
    rw [hr2] at e1 e2
    have : (2 : ℂ) * z = 0 := by
      linear_combination 2 * e1 - 2 * Complex.I * e2 + (z - (starRingEnd ℂ) z) * Complex.I_sq
    simpa using this
  · intro hU a Ψ _
    unfold BookProof.ChapterReconstruct.offDiag
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with hkb
    · rfl
    · have h := hU a b k (Ne.symm hkb)
      linear_combination (Ψ k * (starRingEnd ℂ) (Ψ b)) * h

