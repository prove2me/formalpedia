-- Prove2me | solution 1 for DerivativeChainContinuation.finite_return_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:16:21.992549+00:00
-- url     : https://prove2.me/submissions/94867488-600b-46ca-b23b-8648fbf9eeb0

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainPrivate_exists_nonpos_of_probability_mean_zero
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



theorem finite_weighted_square_bound {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    (∑ i, w i*f i)^2 ≤ ∑ i, w i*(f i)^2 := by
  have h1 (i : ι) : Real.sqrt (w i)*(Real.sqrt (w i)*f i)=w i*f i := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hw i)]
  have h2 (i : ι) : (Real.sqrt (w i)*f i)^2=w i*(f i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i)*f i)
  simpa only [h1,h2,Real.sq_sqrt (hw _),hs,one_mul] using hh

theorem finite_weighted_exists_le_mean {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    ∃ i, f i ≤ ∑ j, w j*f j := by
  have he : (∑ i, w i*(f i-∑ j, w j*f j))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul,sub_self]
  obtain ⟨i,hi⟩ := DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero w _ hw hs he
  exact ⟨i,by linarith⟩

end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {ι : Type} [Fintype ι]
    (w f g : ι → ℝ) (d : ℕ) (V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfg : (∑ i, w i*(f i)^2) ≤ (d:ℝ)*(∑ i, w i*(g i)^2))
    (hV : (∑ i, w i*(g i)^2) ≤ V) :
    ∃ i, f i+g i ≤ (1+Real.sqrt d)*Real.sqrt V := by
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)).trans hV
  have hfn : 0 ≤ ∑ i, w i*f i := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hf i)
  have hgn : 0 ≤ ∑ i, w i*g i := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hg i)
  have hfsq := (finite_weighted_square_bound w f hw hs).trans
    (hfg.trans (mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)))
  have hgsq := (finite_weighted_square_bound w g hw hs).trans hV
  have hrhs : (Real.sqrt d*Real.sqrt V)^2=(d:ℝ)*V := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt hV0]
  have hfl : (∑ i, w i*f i) ≤ Real.sqrt d*Real.sqrt V := by
    rw [← hrhs] at hfsq
    exact (sq_le_sq₀ hfn (by positivity)).mp hfsq
  have hgl : (∑ i, w i*g i) ≤ Real.sqrt V := by
    rw [← Real.sq_sqrt hV0] at hgsq
    exact (sq_le_sq₀ hgn (Real.sqrt_nonneg _)).mp hgsq
  obtain ⟨i,hi⟩ := finite_weighted_exists_le_mean w (fun i => f i+g i) hw hs
  refine ⟨i,hi.trans ?_⟩
  rw [show (∑ i, w i*(f i+g i))=(∑ i, w i*f i)+(∑ i, w i*g i) by simp [mul_add,Finset.sum_add_distrib]]
  nlinarith
