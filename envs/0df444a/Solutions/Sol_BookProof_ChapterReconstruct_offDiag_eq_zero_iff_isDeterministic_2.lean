-- Prove2me | solution 2 for BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T12:39:45.39851+00:00
-- url     : https://prove2.me/submissions/0e92c460-f536-4b2b-b17c-4741f8ffd119

-- Generated from ChapterReconstruct.lean — theorem BookProof.ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic
import Mathlib
import Definitions.Def_ChapterReconstruct
open BookProof.ChapterReconstruct


open scoped BigOperators
open Finset


variable {n : ℕ}
open BookProof.ChapterReconstruct

theorem solution(U : Fin n → Fin n → ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), offDiag U a Ψ = 0) ↔ IsDeterministic U := by
  have hcol : ∀ a : Fin n, (∀ Ψ : Fin n → ℂ, BookProof.ChapterReconstruct.offDiag U a Ψ = 0) ↔ IsDeterministicCol U a := by
    intro a
    constructor
    · intro h l m hlm
      have hev : ∀ w : ℂ, BookProof.ChapterReconstruct.offDiag U a (fun k => if k = m then w else if k = l then 1 else 0) = w * ((starRingEnd ℂ) (U m a) * U l a) + (starRingEnd ℂ) w * ((starRingEnd ℂ) (U l a) * U m a) := by
        intro w
        unfold BookProof.ChapterReconstruct.offDiag
        rw [Fintype.sum_eq_add m l hlm.symm (fun c hc => Finset.sum_eq_zero (fun b _ => by simp [hc.1, hc.2]))]
        rw [Fintype.sum_eq_add m l hlm.symm (fun c hc => by simp [hc.1, hc.2]), Fintype.sum_eq_add m l hlm.symm (fun c hc => by simp [hc.1, hc.2])]
        simp [hlm, hlm.symm]
        ring
      have e1 := hev 1
      have e2 := hev Complex.I
      rw [h] at e1 e2
      apply Complex.ext
      · have r1 := congrArg Complex.re e1
        simp at r1
        simp
        linarith
      · have r2 := congrArg Complex.re e2
        simp at r2
        simp
        linarith
    · intro hD Ψ
      unfold BookProof.ChapterReconstruct.offDiag
      apply Finset.sum_eq_zero
      intro k _
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with hkb
      · rfl
      · have := hD b k (Ne.symm hkb)
        linear_combination (Ψ k * (starRingEnd ℂ) (Ψ b)) * this
  constructor
  · intro h a
    exact (hcol a).mp (h a)
  · intro h a
    exact (hcol a).mpr (h a)
