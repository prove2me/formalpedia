-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_sP_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:56.755904+00:00
-- url     : https://prove2.me/submissions/2163cc6b-8ead-4162-b371-3a6af29d03bb

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagB
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_log_sq_div_sq_primes_tail_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sP_cN_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sP_cN_le_log_div
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
private theorem sum_log_primes_le_mul_log_four' (y : ℕ) :
    ∑ p ∈ (Icc 1 y).filter Nat.Prime, Real.log p ≤ y * Real.log 4 := by
  have hsub : (Icc 1 y).filter Nat.Prime ⊆ (Finset.range (y + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  calc ∑ p ∈ (Icc 1 y).filter Nat.Prime, Real.log p
      ≤ ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
    _ = Real.log (primorial y) := by
        rw [primorial, Nat.cast_prod, Real.log_prod]
        intro p hp
        rw [Finset.mem_filter] at hp
        exact_mod_cast hp.2.ne_zero
    _ ≤ Real.log (4 ^ y) := by
        apply Real.log_le_log
        · exact_mod_cast primorial_pos y
        · exact_mod_cast primorial_le_4_pow y
    _ = y * Real.log 4 := by rw [Real.log_pow]
private theorem sP_cN_le_log_add_sqrt_mul_log_div (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) (hp : p.Prime) :
    sP (cN x) N p ≤ Real.log p + 4 * Real.sqrt x * Real.log p / p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp2
  have hppos : (0:ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set q : ℝ := Real.sqrt p with hq
  have hq2 : q ^ 2 = p := Real.sq_sqrt hppos.le
  have hq0 : 0 < q := Real.sqrt_pos.mpr hppos
  have hq43 : 4 / 3 ≤ q := by nlinarith
  set r : ℝ := 1 / q with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr34 : r ≤ 3 / 4 := by
    rw [hr, div_le_iff₀ hq0]
    linarith
  have hr1 : r < 1 := by linarith
  have hr2 : r ^ 2 = 1 / p := by rw [hr, div_pow, one_pow, hq2]
  set s : ℝ := Real.sqrt x with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx
  have hmin : ∀ k : ℕ, min 1 (x / (p:ℝ) ^ k) ≤ s * r ^ k := by
    intro k
    have ht : x / (p:ℝ) ^ k = (s * r ^ k) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hr2, hs2, one_div, inv_pow, div_eq_mul_inv]
    rw [ht]
    have ha : 0 ≤ s * r ^ k := mul_nonneg hs0 (pow_nonneg hr0 k)
    rcases le_total (s * r ^ k) 1 with h | h
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (min_le_left _ _).trans h
  have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
      (Icc 1 N).image (fun k => p ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hpp, hmf⟩ := hn
    obtain ⟨q', k, hq', hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p = q' := by
      have h1 : p ∣ q' ^ k := by rw [← hmf]; exact Nat.minFac_dvd _
      exact (Nat.prime_dvd_prime_iff_eq hp hq').mp (hp.dvd_of_dvd_pow h1)
    subst hpq
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk, ?_⟩, rfl⟩
    have hlt := Nat.lt_pow_self (by omega : 1 < p) (n := k)
    exact le_of_lt (lt_of_lt_of_le hlt hnN)
  have h4 : r ^ 2 / (1 - r) ≤ 4 / p := by
    have h5 : 1 / (1 - r) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    calc r ^ 2 / (1 - r) = (1 / p) * (1 / (1 - r)) := by rw [hr2]; ring
      _ ≤ (1 / p) * 4 := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 4 / p := by ring
  calc sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
        Real.log p * min 1 (x / n) := by
        unfold sP
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_filter] at hn
        unfold cN
        rw [ArithmeticFunction.vonMangoldt_apply, if_pos hn.2.1, hn.2.2]
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * min 1 (x / n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => mul_nonneg hlog (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n))))
    _ = ∑ k ∈ Icc 1 N, Real.log p * min 1 (x / (p:ℝ) ^ k) := by
        rw [Finset.sum_image (Nat.pow_right_injective hp2).injOn]
        apply Finset.sum_congr rfl
        intro k _
        show Real.log p * min 1 (x / ((p ^ k : ℕ) : ℝ)) = Real.log p * min 1 (x / (p:ℝ) ^ k)
        rw [Nat.cast_pow]
    _ ≤ ∑ k ∈ insert 1 (Ico 2 (N + 1)), Real.log p * min 1 (x / (p:ℝ) ^ k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk
          rw [Finset.mem_insert, Finset.mem_Ico]
          omega
        · intro k _ _
          exact mul_nonneg hlog (le_min zero_le_one (div_nonneg hx (by positivity)))
    _ = Real.log p * min 1 (x / (p:ℝ) ^ 1) +
        ∑ k ∈ Ico 2 (N + 1), Real.log p * min 1 (x / (p:ℝ) ^ k) := by
        rw [Finset.sum_insert]
        simp
    _ ≤ Real.log p * 1 + ∑ k ∈ Ico 2 (N + 1), Real.log p * s * r ^ k := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (min_le_left _ _) hlog
        · apply Finset.sum_le_sum
          intro k _
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hmin k) hlog
    _ = Real.log p + Real.log p * s * ∑ k ∈ Ico 2 (N + 1), r ^ k := by
        rw [mul_one, Finset.mul_sum]
    _ ≤ Real.log p + Real.log p * s * (r ^ 2 / (1 - r)) := by
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (mul_nonneg hlog hs0)
    _ ≤ Real.log p + Real.log p * s * (4 / p) := by
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_left h4 (mul_nonneg hlog hs0)
    _ = Real.log p + 4 * s * Real.log p / p := by ring
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∑ p ∈ (Icc 1 ⌊x ^ 400⌋₊).filter Nat.Prime, sP (cN x) ⌊x ^ 400⌋₊ p ^ 2 ≤ C * x * Real.log x := by
  refine ⟨2000, 3, fun x hx => ?_⟩
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlx : 1 ≤ Real.log x := by
    have he : Real.exp 1 ≤ x := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hL4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hL2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL4' : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    linarith
  have hL2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  set N := ⌊x ^ 400⌋₊ with hN
  set y := ⌊x⌋₊ with hy
  have hy1 : 1 ≤ y := Nat.le_floor (by exact_mod_cast hx1)
  have hyR1 : (1:ℝ) ≤ y := by exact_mod_cast hy1
  have hyx : (y:ℝ) ≤ x := Nat.floor_le hx0
  have hxy : x < (y:ℝ) + 1 := Nat.lt_floor_add_one x
  have hy0 : (0:ℝ) < y := by linarith
  set S1 := (Icc 1 y).filter Nat.Prime with hS1
  set S2 := (Ioc y N).filter Nat.Prime with hS2
  have hsub : (Icc 1 N).filter Nat.Prime ⊆ S1 ∪ S2 := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_union, hS1, hS2, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc]
    by_cases h : p ≤ y
    · left
      exact ⟨⟨hp.1.1, h⟩, hp.2⟩
    · right
      exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have hdisj : Disjoint S1 S2 := by
    rw [hS1, hS2]
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_Ioc] at hb
    omega
  have hsplit : ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN x) N p ^ 2 ≤
      ∑ p ∈ S1, sP (cN x) N p ^ 2 + ∑ p ∈ S2, sP (cN x) N p ^ 2 := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg _)
  have hA : ∑ p ∈ S1, sP (cN x) N p ^ 2 ≤
      2 * (Real.log x * (x * Real.log 4)) + 32 * x * (8 * Real.log 4 * Real.log 2) := by
    have hpt : ∀ p ∈ S1, sP (cN x) N p ^ 2 ≤
        2 * (Real.log x * Real.log p) + 32 * x * (Real.log p ^ 2 / (p:ℝ) ^ 2) := by
      intro p hp
      rw [hS1, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hp1, hpy⟩, hpr⟩ := hp
      have hppos : (0:ℝ) < p := by exact_mod_cast hpr.pos
      have hpx : (p:ℝ) ≤ x := le_trans (by exact_mod_cast hpy) hyx
      have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
      have hlpx : Real.log p ≤ Real.log x := Real.log_le_log hppos hpx
      have h0 := sP_cN_nonneg x hx0 N p
      have h1 := sP_cN_le_log_add_sqrt_mul_log_div x hx0 N p hpr
      have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
      have h2 : sP (cN x) N p ^ 2 ≤ (Real.log p + 4 * Real.sqrt x * Real.log p / p) ^ 2 := by
        nlinarith
      have h3 : (Real.log p + 4 * Real.sqrt x * Real.log p / p) ^ 2 ≤
          2 * Real.log p ^ 2 + 2 * (4 * Real.sqrt x * Real.log p / p) ^ 2 := by
        nlinarith [sq_nonneg (Real.log p - 4 * Real.sqrt x * Real.log p / p)]
      have h4 : (4 * Real.sqrt x * Real.log p / p) ^ 2 =
          16 * x * (Real.log p ^ 2 / (p:ℝ) ^ 2) := by
        rw [div_pow, mul_pow, mul_pow, hs2]
        ring
      have h5 : Real.log p ^ 2 ≤ Real.log x * Real.log p := by nlinarith
      linarith
    have hθ : ∑ p ∈ S1, Real.log p ≤ x * Real.log 4 :=
      (sum_log_primes_le_mul_log_four' y).trans (mul_le_mul_of_nonneg_right hyx hL4)
    have hT : ∑ p ∈ S1, Real.log p ^ 2 / (p:ℝ) ^ 2 ≤ 8 * Real.log 4 * Real.log 2 := by
      have hsub1 : S1 ⊆ (Ioc 1 y).filter Nat.Prime := by
        intro p hp
        rw [hS1, Finset.mem_filter, Finset.mem_Icc] at hp
        rw [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hp.2.one_lt, hp.1.2⟩, hp.2⟩
      have ht := sum_log_sq_div_sq_primes_tail_le y y 1 le_rfl (by omega)
      simp only [Nat.cast_one, Real.log_one, div_one, zero_add] at ht
      calc ∑ p ∈ S1, Real.log p ^ 2 / (p:ℝ) ^ 2
          ≤ ∑ p ∈ (Ioc 1 y).filter Nat.Prime, Real.log p ^ 2 / (p:ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun p _ _ => by positivity)
        _ ≤ 4 * Real.log 4 * (2 * Real.log 2) := ht
        _ = 8 * Real.log 4 * Real.log 2 := by ring
    calc ∑ p ∈ S1, sP (cN x) N p ^ 2
        ≤ ∑ p ∈ S1, (2 * (Real.log x * Real.log p) + 32 * x * (Real.log p ^ 2 / (p:ℝ) ^ 2)) :=
          Finset.sum_le_sum hpt
      _ = 2 * (Real.log x * ∑ p ∈ S1, Real.log p) +
          32 * x * ∑ p ∈ S1, Real.log p ^ 2 / (p:ℝ) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (Real.log x * (x * Real.log 4)) + 32 * x * (8 * Real.log 4 * Real.log 2) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hθ (by linarith)) (by norm_num)
          · exact mul_le_mul_of_nonneg_left hT (by positivity)
  have hB : ∑ p ∈ S2, sP (cN x) N p ^ 2 ≤
      32 * Real.log 4 * x * (Real.log x + 2 * Real.log 2) := by
    have hpt : ∀ p ∈ S2, sP (cN x) N p ^ 2 ≤ 4 * x ^ 2 * (Real.log p ^ 2 / (p:ℝ) ^ 2) := by
      intro p hp
      rw [hS2, Finset.mem_filter] at hp
      have h0 := sP_cN_nonneg x hx0 N p
      have h1 := sP_cN_le_log_div x hx0 N p hp.2
      have h2 : sP (cN x) N p ^ 2 ≤ (2 * x * Real.log p / p) ^ 2 := by nlinarith
      calc sP (cN x) N p ^ 2 ≤ (2 * x * Real.log p / p) ^ 2 := h2
        _ = 4 * x ^ 2 * (Real.log p ^ 2 / (p:ℝ) ^ 2) := by ring
    have ht := sum_log_sq_div_sq_primes_tail_le N N y hy1 (Nat.sub_le N y)
    have hly : Real.log y ≤ Real.log x := Real.log_le_log hy0 hyx
    have hK : 0 ≤ 4 * Real.log 4 * (Real.log x + 2 * Real.log 2) :=
      mul_nonneg (by positivity) (by linarith)
    calc ∑ p ∈ S2, sP (cN x) N p ^ 2
        ≤ ∑ p ∈ S2, 4 * x ^ 2 * (Real.log p ^ 2 / (p:ℝ) ^ 2) := Finset.sum_le_sum hpt
      _ = 4 * x ^ 2 * ∑ p ∈ S2, Real.log p ^ 2 / (p:ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * x ^ 2 * (4 * Real.log 4 * (Real.log x + 2 * Real.log 2) / y) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine ht.trans ?_
          gcongr 4 * Real.log 4 * (?_ + _) / _
      _ ≤ 32 * Real.log 4 * x * (Real.log x + 2 * Real.log 2) := by
          rw [mul_div_assoc', div_le_iff₀ hy0]
          nlinarith [mul_nonneg (mul_nonneg hx0 hK) (by linarith : (0:ℝ) ≤ 2 * y - x)]
  calc ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN x) N p ^ 2
      ≤ ∑ p ∈ S1, sP (cN x) N p ^ 2 + ∑ p ∈ S2, sP (cN x) N p ^ 2 := hsplit
    _ ≤ (2 * (Real.log x * (x * Real.log 4)) + 32 * x * (8 * Real.log 4 * Real.log 2)) +
        32 * Real.log 4 * x * (Real.log x + 2 * Real.log 2) := add_le_add hA hB
    _ ≤ 2000 * x * Real.log x := by
        have hP : x ≤ x * Real.log x := le_mul_of_one_le_right hx0 hlx
        have hxl0 : 0 ≤ x * Real.log x := by linarith
        have h1 : Real.log 4 * (x * Real.log x) ≤ 3 * (x * Real.log x) :=
          mul_le_mul_of_nonneg_right hL4' hxl0
        have h2 : Real.log 4 * Real.log 2 ≤ 3 := by nlinarith
        have h3 : Real.log 4 * Real.log 2 * x ≤ 3 * x := mul_le_mul_of_nonneg_right h2 hx0
        nlinarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
