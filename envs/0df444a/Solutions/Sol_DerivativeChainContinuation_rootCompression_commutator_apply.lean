-- Prove2me | solution 1 for DerivativeChainContinuation.rootCompression_commutator_apply
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:48:38.601694+00:00
-- url     : https://prove2.me/submissions/7ceac419-a66b-4fc2-9b62-007973eb52ea

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
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
open scoped BigOperators
open Matrix







theorem centeringProjection_selfAdjoint (n : ℕ) :
    (centeringProjection n).conjTranspose = centeringProjection n := by
  ext i j
  simp [centeringProjection, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.of_apply, eq_comm]



theorem rootCompression_apply {n : ℕ} (a : Fin n → ℂ) (hc : ∑ i, a i = 0)
    (i j : Fin n) :
    rootCompression a i j = (if i=j then a i else 0) - (a i + a j)/(n : ℂ) := by
  unfold rootCompression centeringProjection
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.mul_apply, Matrix.of_apply]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  simp [hc]
  ring

theorem rootCompression_star {n : ℕ} (a : Fin n → ℂ) :
    (rootCompression a).conjTranspose = rootCompression (fun i => star (a i)) := by
  simp only [rootCompression, conjTranspose_mul, diagonal_conjTranspose,
    centeringProjection_selfAdjoint, Function.comp_def]
  rw [Matrix.mul_assoc]
  rfl



end DerivativeChainContinuation

open DerivativeChainContinuation in
/-- Entry form of the nonnormality identity, with no spectral hypotheses. -/
theorem solution {n : ℕ} (hn : n ≠ 0)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) (i j : Fin n) :
    (rootCompression a * (rootCompression a).conjTranspose -
      (rootCompression a).conjTranspose * rootCompression a) i j =
      (star (a i)*a j-a i*star (a j))/(n : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsc : ∑ i, star (a i) = 0 := by simpa only [star_sum, star_zero] using congrArg (star : ℂ → ℂ) hc
  rw [rootCompression_star]
  simp only [Matrix.sub_apply, Matrix.mul_apply, rootCompression_apply a hc,
    rootCompression_apply _ hsc]
  simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ↓reduceIte]
  have hs (b c : Fin n → ℂ) (hb : ∑ k, b k = 0) (hc' : ∑ k, c k = 0)
      (x y : ℂ) :
      (∑ k, (x+b k)/(n : ℂ)*((c k+y)/(n : ℂ))) =
        ((n : ℂ)*x*y+∑ k, b k*c k)/(n : ℂ)^2 := by
    simp_rw [div_mul_div_comm, ← pow_two]
    rw [← Finset.sum_div]
    congr 1
    simp_rw [add_mul, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    simp [hb, hc', mul_assoc, mul_left_comm]
  rw [hs a (fun k => star (a k)) hc hsc,
    hs (fun k => star (a k)) a hsc hc]
  have hsum : (∑ k, a k*star (a k)) = ∑ k, star (a k)*a k := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  by_cases hij : i=j
  · subst j
    simp only [if_pos rfl]
    field_simp
    ring
  · simp only [if_neg hij]
    field_simp
    ring
