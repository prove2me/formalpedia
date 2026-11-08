-- Prove2me | solution 1 for FuchsThesis.Holevo.eq_3_182
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:31:41.990182+00:00
-- url     : https://prove2.me/submissions/084fd68e-9b1f-4544-9ad1-fb2663bda49c

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Holevo_lyapInv

open scoped ComplexOrder

open FuchsThesis.Holevo in
theorem solution {d : Type} [Fintype d] [DecidableEq d] (ρ A B : Matrix d d ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hL : (1 / 2 : ℂ) • (ρ * lyapInv ρ B + lyapInv ρ B * ρ) = B) :
    (Matrix.trace (ρ * A * lyapInv ρ B)).re ≤ ‖Matrix.trace (ρ * A * lyapInv ρ B)‖ ∧
      (((Matrix.trace (ρ * A * lyapInv ρ B)).re : ℝ) : ℂ) = Matrix.trace (A * B) := by
  have hρH : ρ.IsHermitian := hρ.1.isHermitian
  have hX : (lyapInv ρ B).IsHermitian := by
    unfold lyapInv
    rw [dif_pos hρH]
    have hC : (eigCoord ρ B).IsHermitian := by
      unfold eigCoord
      rw [dif_pos hρH]
      exact Matrix.isHermitian_conjTranspose_mul_mul _ hB
    have hM : (Matrix.of fun j k => if eigval ρ j + eigval ρ k ≠ 0 then
        ((2 / (eigval ρ j + eigval ρ k) : ℝ) : ℂ) * eigCoord ρ B j k else 0).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro j k
      simp only [Matrix.of_apply]
      rw [add_comm (eigval ρ k) (eigval ρ j)]
      split_ifs
      · rw [star_mul', hC.apply j k, Complex.star_def, Complex.conj_ofReal]
      · simp
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hM
  obtain ⟨X, hXd⟩ : ∃ X, X = lyapInv ρ B := ⟨_, rfl⟩
  rw [← hXd] at hL hX ⊢
  refine ⟨Complex.re_le_norm _, ?_⟩
  have hz1 : Matrix.trace (A * ρ * X) = star (Matrix.trace (ρ * A * X)) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hX.eq,
      hA.eq, hρH.eq, Matrix.trace_mul_comm X]
  have hz2 : Matrix.trace (A * X * ρ) = Matrix.trace (ρ * A * X) := Matrix.trace_mul_cycle _ _ _
  have hAB : Matrix.trace (A * B) =
      (1 / 2 : ℂ) * (Matrix.trace (A * ρ * X) + Matrix.trace (A * X * ρ)) := by
    rw [← hL, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, smul_eq_mul]
  rw [hAB, hz1, hz2, Complex.re_eq_add_conj, Complex.star_def]
  ring
