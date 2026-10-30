-- Prove2me | solution 1 for DerivativeChainContinuation.commutator_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:42:20.012764+00:00
-- url     : https://prove2.me/submissions/5c3f359c-ed81-468d-bf65-dc819df4d8a0

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_MatrixEnergy
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators















theorem squareBound_diagonal {n : ℕ} (a : Fin n → ℂ) (r : ℝ)
    (ha : ∀ i, Complex.normSq (a i) ≤ r) : SquareBound (diagonal a) r := by
  intro v
  simp only [vectorSq, Matrix.mulVec_diagonal, map_mul, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (Complex.normSq_nonneg _)





end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

theorem frobeniusSq_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    frobeniusSq M.conjTranspose = frobeniusSq M := by
  simp only [frobeniusSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

theorem frobeniusSq_mul_le {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hM : SquareBound M r) : frobeniusSq (M*N) ≤ r*frobeniusSq N := by
  unfold frobeniusSq
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, Complex.normSq ((M*N) i j)) ≤
        ∑ j, r*(∑ i, Complex.normSq (N i j)) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [vectorSq, Matrix.mulVec, dotProduct, Matrix.mul_apply] using
        hM (fun i => N i j)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

theorem frobeniusSq_mul_le_right {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hN : SquareBound N.conjTranspose r) :
    frobeniusSq (M*N) ≤ r*frobeniusSq M := by
  rw [← frobeniusSq_star (M*N), conjTranspose_mul]
  exact (frobeniusSq_mul_le _ _ r hN).trans_eq (by rw [frobeniusSq_star])

theorem squareBound_diagonal_part {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hM : SquareBound M r) :
    ∀ i, Complex.normSq (M i i) ≤ r := by
  intro i
  have h := hM (Pi.single i 1)
  have he : vectorSq (Pi.single i (1 : ℂ)) = 1 := by simp [vectorSq, Pi.single_apply]
  rw [he, mul_one] at h
  have hh : M*ᵥ(Pi.single i 1) = fun j => M j i := by
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hh] at h
  exact (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (M j i))
    (Finset.mem_univ i)).trans h

theorem frobeniusSq_offDiagonal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    frobeniusSq (M-diagonal (fun i => M i i)) =
      frobeniusSq M - ∑ i, Complex.normSq (M i i) := by
  have he (i j : Fin n) : Complex.normSq ((M-diagonal (fun i => M i i)) i j) =
      Complex.normSq (M i j) - (if i=j then Complex.normSq (M i i) else 0) := by
    by_cases hij : i=j
    · subst j; simp
    · simp [Matrix.sub_apply, Matrix.diagonal_apply, hij]
  simp only [frobeniusSq, he, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem frobeniusSq_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    frobeniusSq (A-B) ≤ 2*(frobeniusSq A+frobeniusSq B) := by
  have he (x y : ℂ) : Complex.normSq (x-y) ≤ 2*(Complex.normSq x+Complex.normSq y) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (x.re+y.re), sq_nonneg (x.im+y.im)]
  simpa only [frobeniusSq, Matrix.sub_apply, Finset.sum_add_distrib,
    ← Finset.mul_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => he (A i j) (B i j)))

end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (r : ℝ)
    (hT : SquareBound T r) (hTs : SquareBound T.conjTranspose r) :
    frobeniusSq (T*T.conjTranspose-T.conjTranspose*T) ≤
      16*r*(frobeniusSq T-∑ i, Complex.normSq (T i i)) := by
  let D := diagonal (fun i => T i i)
  let N := T-D
  have hD : SquareBound D r := squareBound_diagonal _ r (squareBound_diagonal_part T r hT)
  have hDs : SquareBound D.conjTranspose r := by
    rw [diagonal_conjTranspose]
    apply squareBound_diagonal
    intro i
    simpa using squareBound_diagonal_part T r hT i
  have hDD : D*D.conjTranspose = D.conjTranspose*D := by
    simp [D, diagonal_conjTranspose, diagonal_mul_diagonal, mul_comm]
  have hid : T*T.conjTranspose-T.conjTranspose*T =
      (T*N.conjTranspose-N.conjTranspose*T) - (D.conjTranspose*N-N*D.conjTranspose) := by
    dsimp [N]
    simp only [conjTranspose_sub]
    noncomm_ring [hDD]
  have h1 := frobeniusSq_mul_le T N.conjTranspose r hT
  have h2 := frobeniusSq_mul_le_right N.conjTranspose T r hTs
  have h3 := frobeniusSq_mul_le D.conjTranspose N r hDs
  have h4 := frobeniusSq_mul_le_right N D.conjTranspose r
    (by simpa only [conjTranspose_conjTranspose] using hD)
  rw [frobeniusSq_star] at h1 h2
  have hb1 := frobeniusSq_sub_le (T*N.conjTranspose) (N.conjTranspose*T)
  have hb2 := frobeniusSq_sub_le (D.conjTranspose*N) (N*D.conjTranspose)
  have hb := frobeniusSq_sub_le (T*N.conjTranspose-N.conjTranspose*T)
    (D.conjTranspose*N-N*D.conjTranspose)
  rw [← hid] at hb
  have hN : frobeniusSq N = frobeniusSq T-∑ i, Complex.normSq (T i i) :=
    frobeniusSq_offDiagonal T
  rw [← hN]
  linarith
