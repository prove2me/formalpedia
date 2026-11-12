-- Prove2me | solution 1 for FuchsThesis.Helstrom.eq_3_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:34:21.888168+00:00
-- url     : https://prove2.me/submissions/cdafa76d-f04e-4a17-950e-ed65dff71709

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Helstrom_gammaOp

open scoped ComplexOrder

open FuchsThesis.Helstrom in
theorem solution {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ) (hπ0 : 0 ≤ π0)
    (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (γ : n → ℝ)
    (hΓ : gammaOp π0 π1 ρ0 ρ1 = U * Matrix.diagonal (fun j => (γ j : ℂ)) * star U) :
    (∀ t : n → ℝ, (∀ j, 0 ≤ t j ∧ t j ≤ 1) →
      ∃ E0 : Matrix n n ℂ, E0.PosSemidef ∧ (1 - E0).PosSemidef ∧
        (∀ j, γ j < 0 → (star U * E0 * U) j j = 1) ∧
        (∀ j, 0 < γ j → (star U * E0 * U) j j = 0) ∧
        (∀ j, γ j = 0 → (star U * E0 * U) j j = (t j : ℂ))) ∧
    ∀ E0 : Matrix n n ℂ, E0.PosSemidef → (1 - E0).PosSemidef →
      (∀ j, γ j < 0 → (star U * E0 * U) j j = 1) →
      (∀ j, 0 < γ j → (star U * E0 * U) j j = 0) →
      (Matrix.trace (gammaOp π0 π1 ρ0 ρ1 * E0)).re = ∑ j, min (γ j) 0 := by
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨e, he⟩ : ∃ e : n → ℝ,
        e = fun j => if γ j < 0 then 1 else if 0 < γ j then 0 else t j := ⟨_, rfl⟩
    have he01 : ∀ j, 0 ≤ e j ∧ e j ≤ 1 := by
      intro j
      rw [he]
      dsimp only
      split_ifs
      · norm_num
      · norm_num
      · exact ht j
    have heneg : ∀ j, γ j < 0 → e j = 1 := by
      intro j h
      rw [he]
      dsimp only
      rw [if_pos h]
    have hepos : ∀ j, 0 < γ j → e j = 0 := by
      intro j h
      rw [he]
      dsimp only
      rw [if_neg (not_lt.2 h.le), if_pos h]
    have hezero : ∀ j, γ j = 0 → e j = t j := by
      intro j h
      rw [he]
      dsimp only
      rw [if_neg (by rw [h]; exact lt_irrefl 0), if_neg (by rw [h]; exact lt_irrefl 0)]
    obtain ⟨D, hD⟩ : ∃ D : Matrix n n ℂ, D = Matrix.diagonal (fun j => (e j : ℂ)) := ⟨_, rfl⟩
    have hDpsd : D.PosSemidef := by
      rw [hD]
      exact Matrix.PosSemidef.diagonal (fun j => Complex.zero_le_real.2 (he01 j).1)
    have hD1psd : (1 - D).PosSemidef := by
      rw [hD, ← Matrix.diagonal_one, Matrix.diagonal_sub]
      exact Matrix.PosSemidef.diagonal (fun j => by
        show (0 : ℂ) ≤ 1 - (e j : ℂ)
        rw [show (1 : ℂ) - (e j : ℂ) = ((1 - e j : ℝ) : ℂ) by norm_num]
        exact Complex.zero_le_real.2 (by linarith [(he01 j).2]))
    have hconj : ∀ M : Matrix n n ℂ, M.PosSemidef → (U * M * star U).PosSemidef := by
      intro M hM
      have := hM.conjTranspose_mul_mul_same (star U)
      rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at this
    have hM : star U * (U * D * star U) * U = D := by
      rw [show star U * (U * D * star U) * U = (star U * U) * D * (star U * U) by
        simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
    have hDjj : ∀ j, D j j = (e j : ℂ) := by
      intro j
      rw [hD, Matrix.diagonal_apply_eq]
    refine ⟨U * D * star U, hconj D hDpsd, ?_, ?_, ?_, ?_⟩
    · have h1E : 1 - U * D * star U = U * (1 - D) * star U := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU']
      rw [h1E]
      exact hconj _ hD1psd
    · intro j h
      rw [hM, hDjj, heneg j h]
      norm_num
    · intro j h
      rw [hM, hDjj, hepos j h]
      norm_num
    · intro j h
      rw [hM, hDjj, hezero j h]
  · intro E0 _ _ hneg hpos
    rw [hΓ]
    have htr : Matrix.trace (U * Matrix.diagonal (fun j => (γ j : ℂ)) * star U * E0) =
        Matrix.trace (Matrix.diagonal (fun j => (γ j : ℂ)) * (star U * E0 * U)) := by
      rw [show U * Matrix.diagonal (fun j => (γ j : ℂ)) * star U * E0 =
          U * (Matrix.diagonal (fun j => (γ j : ℂ)) * star U * E0) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm,
        show Matrix.diagonal (fun j => (γ j : ℂ)) * star U * E0 * U =
          Matrix.diagonal (fun j => (γ j : ℂ)) * (star U * E0 * U) by simp only [Matrix.mul_assoc]]
    rw [htr]
    have hterm : ∀ j, (γ j : ℂ) * (star U * E0 * U) j j = ((min (γ j) 0 : ℝ) : ℂ) := by
      intro j
      rcases lt_trichotomy (γ j) 0 with h | h | h
      · rw [hneg j h, min_eq_left h.le, mul_one]
      · rw [h, min_self]
        simp
      · rw [hpos j h, min_eq_right h.le, mul_zero, Complex.ofReal_zero]
    have hsum : Matrix.trace (Matrix.diagonal (fun j => (γ j : ℂ)) * (star U * E0 * U)) =
        ∑ j, (γ j : ℂ) * (star U * E0 * U) j j := by
      simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    rw [hsum, Finset.sum_congr rfl (fun j _ => hterm j), ← Complex.ofReal_sum, Complex.ofReal_re]
