-- Prove2me | solution 1 for FermionModewise.fcm_real_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:44:31.926931+00:00
-- url     : https://prove2.me/submissions/5d62f4c0-68db-4c6b-811f-04594cc7b54e

import Mathlib
import Definitions.Def_FermionModewise_fcm

open Matrix

open FermionModewise in
theorem solution {ι ν : Type} [Fintype ι] (γ : ν → Matrix ι ι ℂ)
    (hγ : ∀ α, (γ α)ᴴ = γ α) :
    (∀ ρ : Matrix ι ι ℂ, ρᴴ = ρ → ∀ α β,
      ((1 / (2 * Complex.I)) * Matrix.trace (ρ * (γ α * γ β - γ β * γ α))).im = 0 ∧
      (1 / (2 * Complex.I)) * Matrix.trace (ρ * (γ β * γ α - γ α * γ β)) =
        -((1 / (2 * Complex.I)) * Matrix.trace (ρ * (γ α * γ β - γ β * γ α)))) ∧
    ∀ ψ : ι → ℂ,
      (∀ α β, ((1 / (2 * Complex.I)) * (star ψ ⬝ᵥ ((γ α * γ β - γ β * γ α) *ᵥ ψ))).im = 0) ∧
      (fcm γ ψ)ᵀ = -fcm γ ψ := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    rw [div_eq_iff (by simp [Complex.I_ne_zero])]
    ring_nf
    simp [Complex.I_sq]
  have P1 : ∀ ρ : Matrix ι ι ℂ, ρᴴ = ρ → ∀ α β,
      ((1 / (2 * Complex.I)) * Matrix.trace (ρ * (γ α * γ β - γ β * γ α))).im = 0 := by
    intro ρ hρ α β
    set C := γ α * γ β - γ β * γ α with hC
    have hCH : Cᴴ = -C := by
      rw [hC, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hγ, hγ, neg_sub]
    have hstar : star (Matrix.trace (ρ * C)) = -Matrix.trace (ρ * C) := by
      rw [← trace_conjTranspose, conjTranspose_mul, hCH, hρ, Matrix.neg_mul, trace_neg,
        trace_mul_comm]
    have hre : (Matrix.trace (ρ * C)).re = 0 := by
      have := congrArg Complex.re hstar
      rw [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    rw [hI, Complex.mul_im, hre]
    simp
  refine ⟨fun ρ hρ α β => ⟨P1 ρ hρ α β, ?_⟩, fun ψ => ⟨fun α β => ?_, ?_⟩⟩
  · rw [← neg_sub (γ α * γ β) (γ β * γ α), Matrix.mul_neg, trace_neg, mul_neg]
  · have hdot : star ψ ⬝ᵥ ((γ α * γ β - γ β * γ α) *ᵥ ψ) =
        Matrix.trace (vecMulVec ψ (star ψ) * (γ α * γ β - γ β * γ α)) := by
      simp only [dotProduct, mulVec, Matrix.trace, Matrix.diag, Matrix.mul_apply,
        vecMulVec_apply, Pi.star_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hρ : (vecMulVec ψ (star ψ))ᴴ = vecMulVec ψ (star ψ) := by
      ext i j
      simp [vecMulVec_apply, conjTranspose_apply, mul_comm]
    rw [hdot]
    exact P1 _ hρ α β
  · ext α β
    simp only [fcm, Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply]
    rw [← neg_sub (γ α * γ β) (γ β * γ α), neg_mulVec, dotProduct_neg, mul_neg, Complex.neg_re]
