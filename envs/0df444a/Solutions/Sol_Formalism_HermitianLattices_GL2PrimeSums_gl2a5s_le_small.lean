-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_le_small
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:06:30.483873+00:00
-- url     : https://prove2.me/submissions/1b17fa5f-6c24-4e52-8511-3abd2d99315f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
private theorem capTail {p x : ℝ} (hp : 2 ≤ p) (hx : 0 ≤ x) (m t k : ℕ) :
    (∑ j ∈ range k, min 1 (x / p ^ (m+j))) ≤ (t : ℝ) + 2*x / p^(m+t) := by
  have hp0 : 0 < p := by linarith
  induction k generalizing m t with
  | zero => simp only [sum_range_zero]; positivity
  | succ k ih =>
    rw [sum_range_succ']; simp only [Nat.add_zero]
    have hs : (∑ j ∈ range k, min (1:ℝ) (x / p^(m+(j+1)))) =
        ∑ j ∈ range k, min 1 (x / p^((m+1)+j)) := by
      apply sum_congr rfl; intro j _; rw [show m+(j+1)=(m+1)+j by omega]
    rw [hs]
    cases t with
    | zero =>
      have H := ih (m+1) 0; simp only [Nat.cast_zero,zero_add,Nat.add_zero] at H ⊢
      have htail : 2*x / p^(m+1) ≤ x / p^m := by
        rw [pow_succ, div_le_div_iff₀ (mul_pos (pow_pos hp0 _) hp0) (pow_pos hp0 _)]; nlinarith [mul_nonneg (mul_nonneg hx (pow_nonneg hp0.le m)) (sub_nonneg.mpr hp)]
      calc
        _ ≤ x / p^m + x / p^m := add_le_add (H.trans htail) (min_le_right _ _)
        _ = 2*x / p^m := by ring
    | succ t =>
      have H := ih (m+1) t; rw [show m+(t+1)=(m+1)+t by omega]; push_cast; linarith [min_le_left (1:ℝ) (x/p^m)]


private theorem capWeight {x : ℝ} (hx : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) (a0 : ℕ) :
    primeTermWeight x N p ≤ Real.log p * ((a0 : ℝ) + 2 * x / (p : ℝ) ^ (a0 + 1)) := by
  classical
  let f (j : ℕ) := p^(j+1)
  let T := (primesLeFinset N).filter (fun n => n.minFac=p)
  have hsub : T ⊆ (range N).image f := by
    intro n hn; obtain ⟨hn,hmin⟩ := mem_filter.mp hn
    obtain ⟨hr,hpp⟩ := mem_filter.mp hn
    obtain ⟨q,k,hq,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have eqp : q = p := by simpa [Nat.pow_minFac hk.ne', hq.minFac_eq] using hmin
    subst q; obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    refine mem_image.mpr ⟨j,mem_range.mpr ?_,rfl⟩
    exact (Nat.lt_succ_self j).trans_le ((Nat.lt_pow_self hp.one_lt : j.succ < p^j.succ).le.trans (mem_Icc.mp hr).2)
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  calc
    _ ≤ ∑ n ∈ (range N).image f, cn x n := sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by unfold cn; exact mul_nonneg (vonMangoldt_nonneg) (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg _))))
    _ = ∑ j ∈ range N, cn x (p^(j+1)) := sum_image (fun i _ j _ he => by have := Nat.pow_right_injective hp.two_le he; omega)
    _ = Real.log p * ∑ j ∈ range N, min 1 (x / (p:ℝ)^(1+j)) := by
      rw [mul_sum]; apply sum_congr rfl; intro j _; simp [cn,vonMangoldt_apply_pow,vonMangoldt_apply_prime hp,Nat.add_comm]
    _ ≤ Real.log p * ((a0:ℝ) + 2*x / (p:ℝ)^(a0+1)) := by
      apply mul_le_mul_of_nonneg_left _ hlog; simpa [Nat.add_comm] using capTail (p := (p:ℝ)) (by exact_mod_cast hp.two_le) hx 1 a0 N


theorem solution {x : ℝ} (hx : 1 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    primeTermWeight x N p ≤ Real.log x + 2 * Real.log p := by
  let a := ⌊Real.log x / Real.log (p:ℝ)⌋₊
  have hpp : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : 0 < (p:ℝ) := by linarith
  have hl := Real.log_pos hpp
  have hx0 : 0 < x := by linarith
  have ha : (a:ℝ) ≤ Real.log x / Real.log p := Nat.floor_le (div_nonneg (Real.log_nonneg hx) hl.le)
  have hb : Real.log x / Real.log p < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have h1 := (le_div_iff₀ hl).mp ha
  have h2 := (div_lt_iff₀ hl).mp hb
  have hpow : x ≤ (p:ℝ)^(a+1) := by
    apply (Real.log_le_log_iff hx0 (pow_pos hp0 _)).mp
    rw [Real.log_pow]; push_cast; exact h2.le
  have htail : 2*x / (p:ℝ)^(a+1) ≤ 2 := (div_le_iff₀ (pow_pos hp0 _)).mpr (by linarith)
  calc
    _ ≤ _ := capWeight hx0.le N hp a
    _ ≤ Real.log p * ((a:ℝ)+2) := mul_le_mul_of_nonneg_left (add_le_add (le_refl (a : ℝ)) htail) hl.le
    _ ≤ _ := by linarith
