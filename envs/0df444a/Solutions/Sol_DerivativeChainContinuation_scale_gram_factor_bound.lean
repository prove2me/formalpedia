-- Prove2me | solution 1 for DerivativeChainContinuation.scale_gram_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:16:37.521838+00:00
-- url     : https://prove2.me/submissions/c750c7bf-37aa-4aac-b8c3-59414d6b88f9

import Mathlib
import Definitions.Def_DerivativeChainContinuation_ScaleMoments
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_complex_cauchy
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators







theorem scaleWeight_nonneg {n : ℕ} (a : Fin n → ℂ) (t : ℝ) (ht : 0 < t) (i : Fin n) :
    0 ≤ scaleWeight a t i := by
  exact div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (add_nonneg ht.le (Complex.normSq_nonneg _))

theorem scale_weighted_energy {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (t : ℝ) (ht : 0 < t) :
    (∑ i,scaleWeight a t i*Complex.normSq (a i))=1-t*scaleMeanZero a t := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have he (i : Fin n) : scaleWeight a t i*Complex.normSq (a i)=(n:ℝ)⁻¹-t*scaleWeight a t i := by
    have hd : t+Complex.normSq (a i) ≠ 0 := (add_pos_of_pos_of_nonneg ht (Complex.normSq_nonneg _)).ne'
    unfold scaleWeight
    field_simp [hd,hnR]
    ring
  simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,scaleMeanZero,mul_inv_cancel₀ hnR]


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (t : ℝ) (ht : 0 < t) :
    0 ≤ scaleGramFactor a t ∧ t*scaleGramFactor a t ≤ t*scaleMeanZero a t ∧
      t*scaleMeanZero a t ≤ 1 := by
  have hw := scaleWeight_nonneg a t ht
  have he := scale_weighted_energy hn a t ht
  have hc := finite_weighted_complex_cauchy (scaleWeight a t) a hw
  change Complex.normSq (scaleMeanOne a t) ≤ scaleMeanZero a t*(∑ i,scaleWeight a t i*Complex.normSq (a i)) at hc
  rw [he] at hc
  have henergy : 0 ≤ ∑ i,scaleWeight a t i*Complex.normSq (a i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Complex.normSq_nonneg _)
  refine ⟨add_nonneg (mul_nonneg ht.le (sq_nonneg _)) (Complex.normSq_nonneg _),?_,?_⟩
  · have hh : scaleGramFactor a t ≤ scaleMeanZero a t := by unfold scaleGramFactor; nlinarith
    exact mul_le_mul_of_nonneg_left hh ht.le
  · linarith
