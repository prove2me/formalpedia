-- Prove2me | solution 1 for BroughanRH.extraordinary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:12:21.121305+00:00
-- url     : https://prove2.me/submissions/959af2b0-9a78-44b1-8420-7d2167bc0c8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_robin
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Mathlib

open Finset Real Filter Topology

namespace BRHGron

noncomputable def G (n : ℕ) : ℝ :=
  ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))

lemma sigma_div_eq (n : ℕ) (hn : 0 < n) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / n = ∑ d ∈ n.divisors, (1 / (d : ℝ)) := by
  rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_div hd' hd0]; field_simp

lemma sigma_div_mono {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a ∣ b) :
    ((ArithmeticFunction.sigma 1 a : ℕ) : ℝ) / a ≤ ((ArithmeticFunction.sigma 1 b : ℕ) : ℝ) / b := by
  rw [sigma_div_eq a ha, sigma_div_eq b hb]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hb.ne' h)
    (fun _ _ _ => by positivity)

/-- primes up to `Y` -/
def P (Y : ℕ) : Finset ℕ := (Finset.range (Y + 1)).filter Nat.Prime

def e (p Y : ℕ) : ℕ := 2 * (Nat.log p Y + 1)

def K (Y : ℕ) : ℕ := ∏ p ∈ P Y, p ^ e p Y

lemma mem_P {p Y : ℕ} (h : p ∈ P Y) : p.Prime ∧ p ≤ Y := by
  simp only [P, mem_filter, mem_range] at h; exact ⟨h.2, by omega⟩

lemma K_pos (Y : ℕ) : 0 < K Y :=
  prod_pos fun p hp => pow_pos (mem_P hp).1.pos _

lemma sigma_K (Y : ℕ) :
    ArithmeticFunction.sigma 1 (K Y) = ∏ p ∈ P Y, ArithmeticFunction.sigma 1 (p ^ e p Y) := by
  rw [K, ArithmeticFunction.IsMultiplicative.map_prod _ ArithmeticFunction.isMultiplicative_sigma]
  intro p hp q hq hpq
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (mem_P hp).1 (mem_P hq).1).2 hpq)

lemma Ysq_le (p Y : ℕ) (hp : p.Prime) : (Y : ℝ) ^ 2 ≤ (p : ℝ) ^ e p Y := by
  have h1 : Y < p ^ (Nat.log p Y).succ := Nat.lt_pow_succ_log_self hp.one_lt Y
  have h2 : (Y : ℝ) ≤ (p : ℝ) ^ (Nat.log p Y + 1) := by exact_mod_cast h1.le
  rw [e, mul_comm, pow_mul]
  gcongr

lemma local_bound (p Y : ℕ) (hp : p.Prime) (hY : 1 ≤ Y) :
    (1 - 1 / (Y : ℝ) ^ 2) / (1 - 1 / (p : ℝ)) ≤
      ((ArithmeticFunction.sigma 1 (p ^ e p Y) : ℕ) : ℝ) / ((p ^ e p Y : ℕ) : ℝ) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  set q : ℝ := (p : ℝ) ^ e p Y with hq
  have hqY : (Y : ℝ) ^ 2 ≤ q := Ysq_le p Y hp
  have hq0 : 0 < q := by positivity
  have hgeom : ((∑ i ∈ range (e p Y + 1), p ^ i : ℕ) : ℝ) * ((p : ℝ) - 1) = p * q - 1 := by
    push_cast
    rw [geom_sum_mul, pow_succ, hq]; ring
  have hs : ((∑ i ∈ range (e p Y + 1), p ^ i : ℕ) : ℝ) = (p * q - 1) / ((p : ℝ) - 1) := by
    have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [← hgeom, mul_div_assoc, div_self hp1', mul_one]
  rw [hs]
  push_cast
  rw [← hq]
  have hY2 : (0 : ℝ) < (Y : ℝ) ^ 2 := by positivity
  rw [div_div, div_le_div_iff₀ (by
      have : (0:ℝ) < 1 - 1 / (p : ℝ) := by
        rw [sub_pos, div_lt_one (by linarith)]; exact hp1
      exact this) (by nlinarith)]
  have key : (p : ℝ) * q / (Y : ℝ) ^ 2 ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ hY2]; nlinarith
  field_simp
  have : (p : ℝ) * q ≥ (Y : ℝ) ^ 2 := by rw [ge_iff_le, le_div_iff₀ hY2] at key; linarith
  nlinarith

lemma prod_one_sub_ge (Y : ℕ) (hY : 2 ≤ Y) :
    1 - ((Y : ℝ) + 1) / (Y : ℝ) ^ 2 ≤ (1 - 1 / (Y : ℝ) ^ 2) ^ (P Y).card := by
  have hY0 : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hcard : ((P Y).card : ℝ) ≤ Y + 1 := by
    have : (P Y).card ≤ Y + 1 := by
      have := card_filter_le (range (Y + 1)) Nat.Prime; simpa [P] using this
    exact_mod_cast this
  have hb := one_add_mul_le_pow (a := -(1 / (Y : ℝ) ^ 2)) (by
    have : 1 / (Y : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith) (P Y).card
  have hx : 0 ≤ 1 / (Y : ℝ) ^ 2 := by positivity
  calc 1 - ((Y : ℝ) + 1) / (Y : ℝ) ^ 2 = 1 + -(((Y : ℝ) + 1) * (1 / (Y : ℝ) ^ 2)) := by ring
    _ ≤ 1 + (P Y).card * -(1 / (Y : ℝ) ^ 2) := by nlinarith
    _ ≤ _ := by simpa [sub_eq_add_neg] using hb

lemma mertens_nat (Y : ℕ) :
    ArtinPrimitiveRoots.mertensProduct (Y : ℝ) = ∏ p ∈ P Y, (1 - 1 / (p : ℝ)) := by
  simp [ArtinPrimitiveRoots.mertensProduct, P]

lemma mertens_pos (Y : ℕ) : 0 < ArtinPrimitiveRoots.mertensProduct (Y : ℝ) := by
  rw [mertens_nat]
  apply prod_pos; intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_P hp).1.one_lt
  rw [sub_pos, div_lt_one (by linarith)]; exact hp1

lemma sigmaK_bound (Y : ℕ) (hY : 2 ≤ Y) :
    (1 - ((Y : ℝ) + 1) / (Y : ℝ) ^ 2) / ArtinPrimitiveRoots.mertensProduct (Y : ℝ) ≤
      ((ArithmeticFunction.sigma 1 (K Y) : ℕ) : ℝ) / (K Y : ℝ) := by
  rw [sigma_K, K]
  push_cast
  rw [← prod_div_distrib]
  have h1 : ∏ p ∈ P Y, (1 - 1 / (Y : ℝ) ^ 2) / (1 - 1 / (p : ℝ)) ≤
      ∏ p ∈ P Y, ((ArithmeticFunction.sigma 1 (p ^ e p Y) : ℕ) : ℝ) / ((p : ℝ) ^ e p Y) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_P hp).1.one_lt
      have hY0 : (2 : ℝ) ≤ Y := by exact_mod_cast hY
      apply div_nonneg
      · rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
      · rw [sub_nonneg, div_le_one (by linarith)]; exact hp1.le
    · intro p hp
      have := local_bound p Y (mem_P hp).1 (by omega)
      push_cast at this; exact this
  refine le_trans ?_ h1
  rw [prod_div_distrib, prod_const, ← mertens_nat]
  exact div_le_div_of_nonneg_right (prod_one_sub_ge Y hY) (mertens_pos Y).le

lemma logK_le (Y : ℕ) (hY : 1 ≤ Y) : Real.log (K Y) ≤ 24 * Y := by
  rw [K]; push_cast
  rw [Real.log_prod (fun p hp => by have := (mem_P hp).1.pos; positivity)]
  simp_rw [Real.log_pow]
  have hpsi := Chebyshev.psi_le_const_mul_self (x := (Y : ℝ)) (by positivity)
  rw [Chebyshev.psi_eq_sum_mul_log_prime] at hpsi
  have hl4 : Real.log 4 < 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith
  have h : ∑ p ∈ P Y, ((e p Y : ℕ) : ℝ) * Real.log p ≤
      4 * ∑ p ∈ Nat.primesLE Y, ((Nat.log p Y : ℕ) : ℝ) * Real.log p := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp, hpY⟩ := mem_P hp
    have hl : 1 ≤ Nat.log p Y := Nat.log_pos hpp.one_lt hpY
    have hlr : (1 : ℝ) ≤ (Nat.log p Y : ℝ) := by exact_mod_cast hl
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    simp only [e]; push_cast
    nlinarith
  have hY0 : (0 : ℝ) ≤ Y := by positivity
  calc _ ≤ 4 * ∑ p ∈ Nat.primesLE Y, ((Nat.log p Y : ℕ) : ℝ) * Real.log p := h
    _ ≤ 4 * ((Real.log 4 + 4) * Y) := by linarith
    _ ≤ 24 * Y := by nlinarith

lemma K_ge (Y : ℕ) (hY : 2 ≤ Y) : Y ^ 2 ≤ K Y := by
  have h2 : 2 ∈ P Y := by simp [P, Nat.prime_two]; omega
  have hd : 2 ^ e 2 Y ∣ K Y := dvd_prod_of_mem _ h2
  have := Nat.le_of_dvd (K_pos Y) hd
  have h3 : ((Y : ℝ)) ^ 2 ≤ ((2 : ℕ) : ℝ) ^ e 2 Y := Ysq_le 2 Y Nat.prime_two
  have h4 : Y ^ 2 ≤ 2 ^ e 2 Y := by exact_mod_cast h3
  omega

lemma tendsto_f (C : ℝ) :
    Tendsto (fun y : ℝ => (1 - (y + 1) / y ^ 2) /
      (ArtinPrimitiveRoots.mertensProduct y * (Real.log y + C))) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have h1 := ArtinPrimitiveRoots.mertens_product
  have hlog := Real.tendsto_log_atTop
  have h2 : Tendsto (fun y => ArtinPrimitiveRoots.mertensProduct y) atTop (𝓝 0) := by
    have := h1.mul (tendsto_inv_atTop_zero.comp hlog)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with y hy
    have : Real.log y ≠ 0 := (Real.log_pos hy).ne'
    simp [Function.comp, this]
  have h3 : Tendsto (fun y => ArtinPrimitiveRoots.mertensProduct y * (Real.log y + C)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) + 0 * C)) := by
    have := h1.add (h2.mul_const C)
    refine this.congr' (Eventually.of_forall fun y => ?_)
    simp only; ring
  rw [zero_mul, add_zero] at h3
  have h4 : Tendsto (fun y : ℝ => 1 - (y + 1) / y ^ 2) atTop (𝓝 (1 - (0 + 0 ^ 2))) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_inv_atTop_zero.add (tendsto_inv_atTop_zero.pow 2))
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    field_simp
  simp at h4
  have := h4.div h3 (Real.exp_pos _).ne'
  rw [Real.exp_neg, one_div, inv_inv] at this
  exact this

/-- Gronwall-type lower bound along multiples. -/
lemma exists_mult (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ k : ℕ, 2 ≤ k ∧ N ≤ k ∧ Real.exp Real.eulerMascheroniConstant - ε < G (k * n) := by
  set C := Real.log (24 + Real.log n) with hC
  have hT := (tendsto_f C).comp tendsto_natCast_atTop_atTop
  have hev := hT.eventually (lt_mem_nhds (show Real.exp Real.eulerMascheroniConstant - ε <
    Real.exp Real.eulerMascheroniConstant by linarith))
  obtain ⟨Y, hY⟩ := (hev.and (eventually_ge_atTop (max N 2))).exists
  obtain ⟨hfY, hYN⟩ := hY
  simp only [Function.comp] at hfY
  have hY2 : 2 ≤ Y := le_trans (le_max_right _ _) hYN
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY2
  have hKY := K_ge Y hY2
  refine ⟨K Y, by nlinarith, by nlinarith [le_max_left N 2], ?_⟩
  -- bounds
  set k := K Y with hk
  have hk0 : 0 < k := K_pos Y
  have hkn : 0 < k * n := Nat.mul_pos hk0 hn
  have hkn4 : (4 : ℝ) ≤ ((k * n : ℕ) : ℝ) := by
    have : 4 ≤ k * n := by nlinarith
    exact_mod_cast this
  have hlog1 : 1 < Real.log ((k * n : ℕ) : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < Real.log (Real.log ((k * n : ℕ) : ℝ)) := Real.log_pos hlog1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hLle : Real.log (Real.log ((k * n : ℕ) : ℝ)) ≤ Real.log Y + C := by
    have e1 : Real.log ((k * n : ℕ) : ℝ) = Real.log k + Real.log n := by
      push_cast; rw [Real.log_mul (by exact_mod_cast hk0.ne') (by exact_mod_cast hn.ne')]
    have hlk := logK_le Y (by omega)
    have : Real.log ((k * n : ℕ) : ℝ) ≤ Y * (24 + Real.log n) := by
      rw [e1]; nlinarith
    calc Real.log (Real.log ((k * n : ℕ) : ℝ)) ≤ Real.log (Y * (24 + Real.log n)) :=
          Real.log_le_log (by linarith) this
      _ = Real.log Y + C := by rw [Real.log_mul (by positivity) (by positivity)]
  have hA : 0 < 1 - ((Y : ℝ) + 1) / (Y : ℝ) ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have hmP := mertens_pos Y
  have hsig := sigmaK_bound Y hY2
  have hmono := sigma_div_mono hk0 hkn (Dvd.intro n rfl)
  have hden : 0 < Real.log Y + C := lt_of_lt_of_le hL0 hLle
  calc Real.exp Real.eulerMascheroniConstant - ε
      < (1 - ((Y : ℝ) + 1) / (Y : ℝ) ^ 2) /
        (ArtinPrimitiveRoots.mertensProduct (Y : ℝ) * (Real.log Y + C)) := hfY
    _ = ((1 - ((Y : ℝ) + 1) / (Y : ℝ) ^ 2) / ArtinPrimitiveRoots.mertensProduct (Y : ℝ)) /
        (Real.log Y + C) := by rw [div_div]
    _ ≤ (((ArithmeticFunction.sigma 1 (k * n) : ℕ) : ℝ) / ((k * n : ℕ) : ℝ)) /
        Real.log (Real.log ((k * n : ℕ) : ℝ)) := by
          apply div_le_div₀ (by positivity) (le_trans hsig hmono) hL0 hLle
    _ = G (k * n) := by rw [G, div_div]

/-- Robin's inequality in the form `G n < e^γ`. -/
lemma G_lt (n : ℕ) (hn : 5040 < n) : G n < Real.exp Real.eulerMascheroniConstant := by
  have h := BroughanRH.robin n hn
  have hn' : (5040 : ℝ) < n := by exact_mod_cast hn
  have hlog1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL : 0 < Real.log (Real.log n) := Real.log_pos hlog1
  rw [G, div_lt_iff₀ (by positivity)]
  linarith

end BRHGron


noncomputable section
open scoped BigOperators

namespace BRHExtra

open BRHGron

def expLower (q : ℝ) : ℝ := ∑ i ∈ Finset.range 30, q ^ i / (Nat.factorial i : ℝ)

def logLower (q : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range 12, ((q-1)/(q+1)) ^ (2*i+1) / (2*i+1 : ℝ)

lemma logLower_le {q : ℝ} (hq : 1 ≤ q) : logLower q ≤ Real.log q := by
  have hp : 0 < q+1 := by linarith
  have ht₀ : 0 ≤ (q-1)/(q+1) := div_nonneg (by linarith) hp.le
  have ht₁ : (q-1)/(q+1) < 1 := (div_lt_one hp).mpr (by linarith)
  have hid : (1+(q-1)/(q+1))/(1-(q-1)/(q+1)) = q := by
    field_simp
    ring
  have hl := Real.sum_range_le_log_div ht₀ ht₁ 12
  rw [hid] at hl
  unfold logLower; linarith

lemma expLower_le {q : ℝ} (hq : 0 ≤ q) : expLower q ≤ Real.exp q :=
  Real.sum_le_exp_of_nonneg hq 30

lemma log_ge (x : ℝ) (k : ℕ) (hx : 2 ^ k ≤ x) :
    k * (0.6931471803 : ℝ) + logLower (x / 2 ^ k) ≤ Real.log x := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hx1 : 1 ≤ x / 2 ^ k := by rw [le_div_iff₀ h2k]; linarith
  have e : Real.log x = k * Real.log 2 + Real.log (x / 2 ^ k) := by
    rw [Real.log_div (by linarith) h2k.ne', Real.log_pow]; ring
  rw [e]
  have := logLower_le hx1
  have := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith

lemma LL_ge (x r1 lo : ℝ) (k j : ℕ) (hx : 2 ^ k ≤ x)
    (h1 : r1 ≤ k * (0.6931471803 : ℝ) + logLower (x / 2 ^ k)) (hr1 : 2 ^ j ≤ r1)
    (h2 : lo ≤ j * (0.6931471803 : ℝ) + logLower (r1 / 2 ^ j)) :
    lo ≤ Real.log (Real.log x) := by
  have hr0 : 0 < r1 := lt_of_lt_of_le (by positivity) hr1
  have hlx : r1 ≤ Real.log x := le_trans h1 (log_ge x k hx)
  have := log_ge r1 j hr1
  have := Real.log_le_log hr0 hlx
  linarith

lemma LL_le (x v w : ℝ) (hx : 1 < x) (h1 : x ≤ expLower v) (hv : 0 ≤ v)
    (h2 : v ≤ expLower w) (hw : 0 ≤ w) : Real.log (Real.log x) ≤ w := by
  have hlx : Real.log x ≤ v := by
    rw [Real.log_le_iff_le_exp (by linarith)]; exact le_trans h1 (expLower_le hv)
  have hl0 : 0 < Real.log x := Real.log_pos hx
  calc Real.log (Real.log x) ≤ Real.log v := Real.log_le_log hl0 hlx
    _ ≤ w := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact le_trans h2 (expLower_le hw)

lemma LL_pos (x : ℝ) (hx : 3 ≤ x) : 0 < Real.log (Real.log x) := by
  apply Real.log_pos
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9; linarith

lemma LL_mono {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    Real.log (Real.log x) ≤ Real.log (Real.log y) := by
  have h1 : 0 < Real.log x := Real.log_pos (by linarith)
  exact Real.log_le_log h1 (Real.log_le_log (by linarith) hxy)

def fastSigma (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.primeFactorsList.count p + 1), p ^ i

lemma sigma_eq_fast (n : ℕ) (hn : n ≠ 0) : ArithmeticFunction.sigma 1 n = fastSigma n := by
  simpa [fastSigma] using
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hn

def floorH (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 1000000 / (i+1)

lemma floorH_le (n : ℕ) :
    (floorH n : ℝ) / 1000000 ≤ (harmonic n : ℝ) := by
  calc
    _ = ∑ i ∈ Finset.range n, ((1000000 / (i+1) : ℕ) : ℝ) / 1000000 := by
      simp [floorH,Finset.sum_div]
    _ ≤ ∑ i ∈ Finset.range n, (((i+1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      have h : ((1000000 / (i+1) : ℕ) : ℝ) ≤ (1000000 : ℝ) / (i+1 : ℕ) :=
        Nat.cast_div_le
      calc
        _ ≤ ((1000000 : ℝ) / (i+1 : ℕ)) / 1000000 :=
          div_le_div_of_nonneg_right h (by norm_num)
        _ = _ := by push_cast; field_simp
    _ = (harmonic n : ℝ) := by simp [harmonic]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma floorH_200 : floorH 200 = 5877945 := by decide +kernel

lemma EG_low : (1776489 : ℝ) / 1000000 ≤ Real.exp Real.eulerMascheroniConstant := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 200
  have hH := floorH_le 200
  rw [floorH_200] at hH
  have hlog : Real.log 201 ≤ (2651653 : ℝ) / 500000 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    refine le_trans ?_ (expLower_le (by norm_num))
    norm_num [expLower, Finset.sum_range_succ]
  have hg : (574639 : ℝ) / 1000000 ≤ Real.eulerMascheroniConstant := by
    have : Real.eulerMascheroniSeq 200 = (harmonic 200 : ℝ) - Real.log 201 := by
      rw [Real.eulerMascheroniSeq]; norm_num
    push_cast at hH
    linarith
  calc (1776489 : ℝ) / 1000000 ≤ expLower ((574639 : ℝ) / 1000000) := by
        norm_num [expLower, Finset.sum_range_succ]
    _ ≤ Real.exp ((574639 : ℝ) / 1000000) := expLower_le (by norm_num)
    _ ≤ _ := Real.exp_le_exp.2 hg

lemma EG_lt_two : Real.exp Real.eulerMascheroniConstant < 2 := by
  have h1 := Real.eulerMascheroniConstant_lt_two_thirds
  have h2 := Real.log_two_gt_d9
  calc Real.exp Real.eulerMascheroniConstant < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.2 (by linarith)
    _ = 2 := Real.exp_log (by norm_num)

def Elist : List ℕ := [3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36, 48, 60, 72, 84, 120, 180, 240, 360, 420, 720, 840, 2520, 5040]

/-- Generic interval step: from `10^6 σ(n) < C n` and `C/10^6 ≤ EG_low * LL(a)` get `G n < e^γ`. -/
lemma G_lt_of (n a C : ℕ) (lo : ℝ) (h3 : 3 ≤ a) (ha : a ≤ n)
    (hc : 1000000 * ArithmeticFunction.sigma 1 n < C * n)
    (hlo : lo ≤ Real.log (Real.log a)) (hC : (C : ℝ) / 1000000 ≤ (1776489 : ℝ) / 1000000 * lo) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have ha3 : (3 : ℝ) ≤ a := by exact_mod_cast h3
  have han : (a : ℝ) ≤ n := by exact_mod_cast ha
  have hLL := LL_mono ha3 han
  have hLLp := LL_pos (n : ℝ) (by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hc' : (1000000 : ℝ) * ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < C * n := by exact_mod_cast hc
  have hEG := EG_low
  rw [G, div_lt_iff₀ (by positivity)]
  have hlo0 : 0 ≤ lo ∨ lo < 0 := le_or_gt 0 lo
  have key : (C : ℝ) * n / 1000000 ≤ Real.exp Real.eulerMascheroniConstant * (n * Real.log (Real.log n)) := by
    have h1 : (C : ℝ) * n / 1000000 = (C / 1000000) * n := by ring
    rw [h1]
    have h2 : (C : ℝ) / 1000000 ≤ Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by
      rcases hlo0 with h | h
      · calc (C : ℝ) / 1000000 ≤ (1776489 : ℝ) / 1000000 * lo := hC
          _ ≤ Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by
            apply mul_le_mul hEG (by linarith) h (by positivity)
      · have : (C : ℝ) / 1000000 ≤ 0 := by nlinarith
        have : 0 ≤ Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by positivity
        linarith
    nlinarith
  linarith


lemma iv0_checked : ((List.range' 5 2).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 845402 * n)) = true := by decide +kernel

lemma iv0 (n : ℕ) (ha : 5 ≤ n) (hb : n < 7) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 5 2 := List.mem_range'.mpr ⟨n - 5, by omega, by omega⟩
  have h := List.all_eq_true.mp iv0_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 845402 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (475884 : ℝ) / 1000000 ≤ Real.log (Real.log ((5 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((1609437 : ℝ) / 1000000) _ 2 0 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 5 845402 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv1_checked : ((List.range' 7 7).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 1182660 * n)) = true := by decide +kernel

lemma iv1 (n : ℕ) (ha : 7 ≤ n) (hb : n < 14) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 7 7 := List.mem_range'.mpr ⟨n - 7, by omega, by omega⟩
  have h := List.all_eq_true.mp iv1_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 1182660 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (665729 : ℝ) / 1000000 ≤ Real.log (Real.log ((7 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((1945910 : ℝ) / 1000000) _ 2 0 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 7 1182660 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv2_checked : ((List.range' 14 14).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 1723942 * n)) = true := by decide +kernel

lemma iv2 (n : ℕ) (ha : 14 ≤ n) (hb : n < 28) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 14 14 := List.mem_range'.mpr ⟨n - 14, by omega, by omega⟩
  have h := List.all_eq_true.mp iv2_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 1723942 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (970421 : ℝ) / 1000000 ≤ Real.log (Real.log ((14 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((2639057 : ℝ) / 1000000) _ 3 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 14 1723942 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv3_checked : ((List.range' 28 12).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 2138240 * n)) = true := by decide +kernel

lemma iv3 (n : ℕ) (ha : 28 ≤ n) (hb : n < 40) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 28 12 := List.mem_range'.mpr ⟨n - 28, by omega, by omega⟩
  have h := List.all_eq_true.mp iv3_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 2138240 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1203633 : ℝ) / 1000000 ≤ Real.log (Real.log ((28 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((3332204 : ℝ) / 1000000) _ 4 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 28 2138240 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv4_checked : ((List.range' 40 40).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 2318889 * n)) = true := by decide +kernel

lemma iv4 (n : ℕ) (ha : 40 ≤ n) (hb : n < 80) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 40 40 := List.mem_range'.mpr ⟨n - 40, by omega, by omega⟩
  have h := List.all_eq_true.mp iv4_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 2318889 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1305322 : ℝ) / 1000000 ≤ Real.log (Real.log ((40 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((3688879 : ℝ) / 1000000) _ 5 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 40 2318889 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv5_checked : ((List.range' 80 16).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 2624781 * n)) = true := by decide +kernel

lemma iv5 (n : ℕ) (ha : 80 ≤ n) (hb : n < 96) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 80 16 := List.mem_range'.mpr ⟨n - 80, by omega, by omega⟩
  have h := List.all_eq_true.mp iv5_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 2624781 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1477511 : ℝ) / 1000000 ≤ Real.log (Real.log ((80 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((4382026 : ℝ) / 1000000) _ 6 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 80 2624781 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv6_checked : ((List.range' 96 48).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 2697198 * n)) = true := by decide +kernel

lemma iv6 (n : ℕ) (ha : 96 ≤ n) (hb : n < 144) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 96 48 := List.mem_range'.mpr ⟨n - 96, by omega, by omega⟩
  have h := List.all_eq_true.mp iv6_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 2697198 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1518275 : ℝ) / 1000000 ≤ Real.log (Real.log ((96 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((4564348 : ℝ) / 1000000) _ 6 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 96 2697198 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv7_checked : ((List.range' 144 24).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 2848390 * n)) = true := by decide +kernel

lemma iv7 (n : ℕ) (ha : 144 ≤ n) (hb : n < 168) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 144 24 := List.mem_range'.mpr ⟨n - 144, by omega, by omega⟩
  have h := List.all_eq_true.mp iv7_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 2848390 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1603382 : ℝ) / 1000000 ≤ Real.log (Real.log ((144 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((4969813 : ℝ) / 1000000) _ 7 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 144 2848390 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv8_checked : ((List.range' 168 168).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 2902654 * n)) = true := by decide +kernel

lemma iv8 (n : ℕ) (ha : 168 ≤ n) (hb : n < 336) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 168 168 := List.mem_range'.mpr ⟨n - 168, by omega, by omega⟩
  have h := List.all_eq_true.mp iv8_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 2902654 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1633928 : ℝ) / 1000000 ≤ Real.log (Real.log ((168 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((5123963 : ℝ) / 1000000) _ 7 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 168 2902654 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv9_checked : ((List.range' 336 144).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 3128046 * n)) = true := by decide +kernel

lemma iv9 (n : ℕ) (ha : 336 ≤ n) (hb : n < 480) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 336 144 := List.mem_range'.mpr ⟨n - 336, by omega, by omega⟩
  have h := List.all_eq_true.mp iv9_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 3128046 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1760803 : ℝ) / 1000000 ≤ Real.log (Real.log ((336 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((5817111 : ℝ) / 1000000) _ 8 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 336 3128046 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv10_checked : ((List.range' 480 600).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 3233763 * n)) = true := by decide +kernel

lemma iv10 (n : ℕ) (ha : 480 ≤ n) (hb : n < 1080) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 480 600 := List.mem_range'.mpr ⟨n - 480, by omega, by omega⟩
  have h := List.all_eq_true.mp iv10_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 3233763 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1820312 : ℝ) / 1000000 ≤ Real.log (Real.log ((480 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((6173786 : ℝ) / 1000000) _ 8 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 480 3233763 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv11_checked : ((List.range' 1080 180).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 3453003 * n)) = true := by decide +kernel

lemma iv11 (n : ℕ) (ha : 1080 ≤ n) (hb : n < 1260) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 1080 180 := List.mem_range'.mpr ⟨n - 1080, by omega, by omega⟩
  have h := List.all_eq_true.mp iv11_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 3453003 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1943724 : ℝ) / 1000000 ≤ Real.log (Real.log ((1080 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((6984716 : ℝ) / 1000000) _ 10 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 1080 3453003 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv12_checked : ((List.range' 1260 420).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 3491782 * n)) = true := by decide +kernel

lemma iv12 (n : ℕ) (ha : 1260 ≤ n) (hb : n < 1680) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 1260 420 := List.mem_range'.mpr ⟨n - 1260, by omega, by omega⟩
  have h := List.all_eq_true.mp iv12_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 3491782 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (1965553 : ℝ) / 1000000 ≤ Real.log (Real.log ((1260 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((7138866 : ℝ) / 1000000) _ 10 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 1260 3491782 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv13_checked : ((List.range' 1680 1680).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 3561968 * n)) = true := by decide +kernel

lemma iv13 (n : ℕ) (ha : 1680 ≤ n) (hb : n < 3360) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 1680 1680 := List.mem_range'.mpr ⟨n - 1680, by omega, by omega⟩
  have h := List.all_eq_true.mp iv13_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 3561968 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (2005061 : ℝ) / 1000000 ≤ Real.log (Real.log ((1680 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((7426549 : ℝ) / 1000000) _ 10 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 1680 3561968 _ (by norm_num) ha hc hlo (by norm_num)


lemma iv14_checked : ((List.range' 3360 1681).all fun n =>
    decide (n ∈ Elist ∨ 1000000 * fastSigma n < 3720486 * n)) = true := by decide +kernel

lemma iv14 (n : ℕ) (ha : 3360 ≤ n) (hb : n < 5041) (hE : n ∉ Elist) :
    G n < Real.exp Real.eulerMascheroniConstant := by
  have hm : n ∈ List.range' 3360 1681 := List.mem_range'.mpr ⟨n - 3360, by omega, by omega⟩
  have h := List.all_eq_true.mp iv14_checked n hm
  simp only [decide_eq_true_eq] at h
  have hc : 1000000 * ArithmeticFunction.sigma 1 n < 3720486 * n := by
    rw [sigma_eq_fast n (by omega)]; tauto
  have hlo : (2094292 : ℝ) / 1000000 ≤ Real.log (Real.log ((3360 : ℕ) : ℝ)) := by
    push_cast
    exact LL_ge _ ((8119696 : ℝ) / 1000000) _ 11 3 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  exact G_lt_of n 3360 3720486 _ (by norm_num) ha hc hlo (by norm_num)


lemma wit6 : G 6 < G 3 := by
  have hs1 : ArithmeticFunction.sigma 1 6 = 12 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 3 = 4 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (583197 : ℝ) / 1000000 ≤ Real.log (Real.log (6 : ℝ)) :=
    LL_ge _ ((1791759 : ℝ) / 1000000) _ 2 0 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (3 : ℝ)) ≤ (94051 : ℝ) / 1000000 :=
    LL_le _ ((1098614 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (6 : ℝ) (by norm_num)
  have hp2 := LL_pos (3 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (12 : ℝ) * (3 * Real.log (Real.log 3)) ≤ 12 * (3 * (94051 / 1000000)) := by gcongr
    _ < 4 * (6 * (583197 / 1000000)) := by norm_num
    _ ≤ 4 * (6 * Real.log (Real.log 6)) := by gcongr


lemma wit8 : G 8 < G 4 := by
  have hs1 : ArithmeticFunction.sigma 1 8 = 15 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 4 = 7 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (732099 : ℝ) / 1000000 ≤ Real.log (Real.log (8 : ℝ)) :=
    LL_ge _ ((2079441 : ℝ) / 1000000) _ 3 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (4 : ℝ)) ≤ (326637 : ℝ) / 1000000 :=
    LL_le _ ((1386296 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (8 : ℝ) (by norm_num)
  have hp2 := LL_pos (4 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (15 : ℝ) * (4 * Real.log (Real.log 4)) ≤ 15 * (4 * (326637 / 1000000)) := by gcongr
    _ < 7 * (8 * (732099 / 1000000)) := by norm_num
    _ ≤ 7 * (8 * Real.log (Real.log 8)) := by gcongr


lemma wit9 : G 9 < G 3 := by
  have hs1 : ArithmeticFunction.sigma 1 9 = 13 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 3 = 4 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (787194 : ℝ) / 1000000 ≤ Real.log (Real.log (9 : ℝ)) :=
    LL_ge _ ((2197224 : ℝ) / 1000000) _ 3 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (3 : ℝ)) ≤ (94051 : ℝ) / 1000000 :=
    LL_le _ ((1098614 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (9 : ℝ) (by norm_num)
  have hp2 := LL_pos (3 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (13 : ℝ) * (3 * Real.log (Real.log 3)) ≤ 13 * (3 * (94051 / 1000000)) := by gcongr
    _ < 4 * (9 * (787194 / 1000000)) := by norm_num
    _ ≤ 4 * (9 * Real.log (Real.log 9)) := by gcongr


lemma wit10 : G 10 < G 5 := by
  have hs1 : ArithmeticFunction.sigma 1 10 = 18 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 5 = 6 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (834032 : ℝ) / 1000000 ≤ Real.log (Real.log (10 : ℝ)) :=
    LL_ge _ ((2302585 : ℝ) / 1000000) _ 3 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (5 : ℝ)) ≤ (475887 : ℝ) / 1000000 :=
    LL_le _ ((1609439 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (10 : ℝ) (by norm_num)
  have hp2 := LL_pos (5 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (18 : ℝ) * (5 * Real.log (Real.log 5)) ≤ 18 * (5 * (475887 / 1000000)) := by gcongr
    _ < 6 * (10 * (834032 / 1000000)) := by norm_num
    _ ≤ 6 * (10 * Real.log (Real.log 10)) := by gcongr


lemma wit12 : G 12 < G 6 := by
  have hs1 : ArithmeticFunction.sigma 1 12 = 28 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 6 = 12 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (910234 : ℝ) / 1000000 ≤ Real.log (Real.log (12 : ℝ)) :=
    LL_ge _ ((2484906 : ℝ) / 1000000) _ 3 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (6 : ℝ)) ≤ (583200 : ℝ) / 1000000 :=
    LL_le _ ((1791761 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (12 : ℝ) (by norm_num)
  have hp2 := LL_pos (6 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (28 : ℝ) * (6 * Real.log (Real.log 6)) ≤ 28 * (6 * (583200 / 1000000)) := by gcongr
    _ < 12 * (12 * (910234 / 1000000)) := by norm_num
    _ ≤ 12 * (12 * Real.log (Real.log 12)) := by gcongr


lemma wit16 : G 16 < G 8 := by
  have hs1 : ArithmeticFunction.sigma 1 16 = 31 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 8 = 15 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1019781 : ℝ) / 1000000 ≤ Real.log (Real.log (16 : ℝ)) :=
    LL_ge _ ((2772588 : ℝ) / 1000000) _ 4 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (8 : ℝ)) ≤ (732102 : ℝ) / 1000000 :=
    LL_le _ ((2079443 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (16 : ℝ) (by norm_num)
  have hp2 := LL_pos (8 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (31 : ℝ) * (8 * Real.log (Real.log 8)) ≤ 31 * (8 * (732102 / 1000000)) := by gcongr
    _ < 15 * (16 * (1019781 / 1000000)) := by norm_num
    _ ≤ 15 * (16 * Real.log (Real.log 16)) := by gcongr


lemma wit18 : G 18 < G 6 := by
  have hs1 : ArithmeticFunction.sigma 1 18 = 39 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 6 = 12 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1061384 : ℝ) / 1000000 ≤ Real.log (Real.log (18 : ℝ)) :=
    LL_ge _ ((2890371 : ℝ) / 1000000) _ 4 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (6 : ℝ)) ≤ (583200 : ℝ) / 1000000 :=
    LL_le _ ((1791761 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (18 : ℝ) (by norm_num)
  have hp2 := LL_pos (6 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (39 : ℝ) * (6 * Real.log (Real.log 6)) ≤ 39 * (6 * (583200 / 1000000)) := by gcongr
    _ < 12 * (18 * (1061384 / 1000000)) := by norm_num
    _ ≤ 12 * (18 * Real.log (Real.log 18)) := by gcongr


lemma wit20 : G 20 < G 10 := by
  have hs1 : ArithmeticFunction.sigma 1 20 = 42 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 10 = 18 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1097188 : ℝ) / 1000000 ≤ Real.log (Real.log (20 : ℝ)) :=
    LL_ge _ ((2995732 : ℝ) / 1000000) _ 4 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (10 : ℝ)) ≤ (834035 : ℝ) / 1000000 :=
    LL_le _ ((2302587 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (20 : ℝ) (by norm_num)
  have hp2 := LL_pos (10 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (42 : ℝ) * (10 * Real.log (Real.log 10)) ≤ 42 * (10 * (834035 / 1000000)) := by gcongr
    _ < 18 * (20 * (1097188 / 1000000)) := by norm_num
    _ ≤ 18 * (20 * Real.log (Real.log 20)) := by gcongr


lemma wit24 : G 24 < G 12 := by
  have hs1 : ArithmeticFunction.sigma 1 24 = 60 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 12 = 28 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1156268 : ℝ) / 1000000 ≤ Real.log (Real.log (24 : ℝ)) :=
    LL_ge _ ((3178053 : ℝ) / 1000000) _ 4 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (12 : ℝ)) ≤ (910237 : ℝ) / 1000000 :=
    LL_le _ ((2484908 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (24 : ℝ) (by norm_num)
  have hp2 := LL_pos (12 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (60 : ℝ) * (12 * Real.log (Real.log 12)) ≤ 60 * (12 * (910237 / 1000000)) := by gcongr
    _ < 28 * (24 * (1156268 / 1000000)) := by norm_num
    _ ≤ 28 * (24 * Real.log (Real.log 24)) := by gcongr


lemma wit30 : G 30 < G 10 := by
  have hs1 : ArithmeticFunction.sigma 1 30 = 72 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 10 = 18 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1224127 : ℝ) / 1000000 ≤ Real.log (Real.log (30 : ℝ)) :=
    LL_ge _ ((3401197 : ℝ) / 1000000) _ 4 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (10 : ℝ)) ≤ (834035 : ℝ) / 1000000 :=
    LL_le _ ((2302587 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (30 : ℝ) (by norm_num)
  have hp2 := LL_pos (10 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (72 : ℝ) * (10 * Real.log (Real.log 10)) ≤ 72 * (10 * (834035 / 1000000)) := by gcongr
    _ < 18 * (30 * (1224127 / 1000000)) := by norm_num
    _ ≤ 18 * (30 * Real.log (Real.log 30)) := by gcongr


lemma wit36 : G 36 < G 18 := by
  have hs1 : ArithmeticFunction.sigma 1 36 = 91 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 18 = 39 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1276344 : ℝ) / 1000000 ≤ Real.log (Real.log (36 : ℝ)) :=
    LL_ge _ ((3583518 : ℝ) / 1000000) _ 5 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (18 : ℝ)) ≤ (1061387 : ℝ) / 1000000 :=
    LL_le _ ((2890373 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (36 : ℝ) (by norm_num)
  have hp2 := LL_pos (18 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (91 : ℝ) * (18 * Real.log (Real.log 18)) ≤ 91 * (18 * (1061387 / 1000000)) := by gcongr
    _ < 39 * (36 * (1276344 / 1000000)) := by norm_num
    _ ≤ 39 * (36 * Real.log (Real.log 36)) := by gcongr


lemma wit48 : G 48 < G 24 := by
  have hs1 : ArithmeticFunction.sigma 1 48 = 124 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 24 = 60 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1353564 : ℝ) / 1000000 ≤ Real.log (Real.log (48 : ℝ)) :=
    LL_ge _ ((3871201 : ℝ) / 1000000) _ 5 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (24 : ℝ)) ≤ (1156271 : ℝ) / 1000000 :=
    LL_le _ ((3178055 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (48 : ℝ) (by norm_num)
  have hp2 := LL_pos (24 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (124 : ℝ) * (24 * Real.log (Real.log 24)) ≤ 124 * (24 * (1156271 / 1000000)) := by gcongr
    _ < 60 * (48 * (1353564 / 1000000)) := by norm_num
    _ ≤ 60 * (48 * Real.log (Real.log 48)) := by gcongr


lemma wit60 : G 60 < G 12 := by
  have hs1 : ArithmeticFunction.sigma 1 60 = 168 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 12 = 28 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1409606 : ℝ) / 1000000 ≤ Real.log (Real.log (60 : ℝ)) :=
    LL_ge _ ((4094344 : ℝ) / 1000000) _ 5 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (12 : ℝ)) ≤ (910237 : ℝ) / 1000000 :=
    LL_le _ ((2484908 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (60 : ℝ) (by norm_num)
  have hp2 := LL_pos (12 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (168 : ℝ) * (12 * Real.log (Real.log 12)) ≤ 168 * (12 * (910237 / 1000000)) := by gcongr
    _ < 28 * (60 * (1409606 / 1000000)) := by norm_num
    _ ≤ 28 * (60 * Real.log (Real.log 60)) := by gcongr


lemma wit72 : G 72 < G 36 := by
  have hs1 : ArithmeticFunction.sigma 1 72 = 195 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 36 = 91 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1453173 : ℝ) / 1000000 ≤ Real.log (Real.log (72 : ℝ)) :=
    LL_ge _ ((4276666 : ℝ) / 1000000) _ 6 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (36 : ℝ)) ≤ (1276347 : ℝ) / 1000000 :=
    LL_le _ ((3583520 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (72 : ℝ) (by norm_num)
  have hp2 := LL_pos (36 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (195 : ℝ) * (36 * Real.log (Real.log 36)) ≤ 195 * (36 * (1276347 / 1000000)) := by gcongr
    _ < 91 * (72 * (1453173 / 1000000)) := by norm_num
    _ ≤ 91 * (72 * Real.log (Real.log 72)) := by gcongr


lemma wit84 : G 84 < G 12 := by
  have hs1 : ArithmeticFunction.sigma 1 84 = 224 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 12 = 28 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1488583 : ℝ) / 1000000 ≤ Real.log (Real.log (84 : ℝ)) :=
    LL_ge _ ((4430816 : ℝ) / 1000000) _ 6 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (12 : ℝ)) ≤ (910237 : ℝ) / 1000000 :=
    LL_le _ ((2484908 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (84 : ℝ) (by norm_num)
  have hp2 := LL_pos (12 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (224 : ℝ) * (12 * Real.log (Real.log 12)) ≤ 224 * (12 * (910237 / 1000000)) := by gcongr
    _ < 28 * (84 * (1488583 / 1000000)) := by norm_num
    _ ≤ 28 * (84 * Real.log (Real.log 84)) := by gcongr


lemma wit120 : G 120 < G 60 := by
  have hs1 : ArithmeticFunction.sigma 1 120 = 360 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 60 = 168 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1566006 : ℝ) / 1000000 ≤ Real.log (Real.log (120 : ℝ)) :=
    LL_ge _ ((4787491 : ℝ) / 1000000) _ 6 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (60 : ℝ)) ≤ (1409608 : ℝ) / 1000000 :=
    LL_le _ ((4094346 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (120 : ℝ) (by norm_num)
  have hp2 := LL_pos (60 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (360 : ℝ) * (60 * Real.log (Real.log 60)) ≤ 360 * (60 * (1409608 / 1000000)) := by gcongr
    _ < 168 * (120 * (1566006 / 1000000)) := by norm_num
    _ ≤ 168 * (120 * Real.log (Real.log 120)) := by gcongr


lemma wit180 : G 180 < G 60 := by
  have hs1 : ArithmeticFunction.sigma 1 180 = 546 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 60 = 168 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1647303 : ℝ) / 1000000 ≤ Real.log (Real.log (180 : ℝ)) :=
    LL_ge _ ((5192956 : ℝ) / 1000000) _ 7 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (60 : ℝ)) ≤ (1409608 : ℝ) / 1000000 :=
    LL_le _ ((4094346 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (180 : ℝ) (by norm_num)
  have hp2 := LL_pos (60 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (546 : ℝ) * (60 * Real.log (Real.log 60)) ≤ 546 * (60 * (1409608 / 1000000)) := by gcongr
    _ < 168 * (180 * (1647303 / 1000000)) := by norm_num
    _ ≤ 168 * (180 * Real.log (Real.log 180)) := by gcongr


lemma wit240 : G 240 < G 120 := by
  have hs1 : ArithmeticFunction.sigma 1 240 = 744 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 120 = 360 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1701221 : ℝ) / 1000000 ≤ Real.log (Real.log (240 : ℝ)) :=
    LL_ge _ ((5480638 : ℝ) / 1000000) _ 7 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (120 : ℝ)) ≤ (1566008 : ℝ) / 1000000 :=
    LL_le _ ((4787493 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (240 : ℝ) (by norm_num)
  have hp2 := LL_pos (120 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (744 : ℝ) * (120 * Real.log (Real.log 120)) ≤ 744 * (120 * (1566008 / 1000000)) := by gcongr
    _ < 360 * (240 * (1701221 / 1000000)) := by norm_num
    _ ≤ 360 * (240 * Real.log (Real.log 240)) := by gcongr


lemma wit360 : G 360 < G 180 := by
  have hs1 : ArithmeticFunction.sigma 1 360 = 1170 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 180 = 546 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1772594 : ℝ) / 1000000 ≤ Real.log (Real.log (360 : ℝ)) :=
    LL_ge _ ((5886104 : ℝ) / 1000000) _ 8 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (180 : ℝ)) ≤ (1647305 : ℝ) / 1000000 :=
    LL_le _ ((5192958 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (360 : ℝ) (by norm_num)
  have hp2 := LL_pos (180 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (1170 : ℝ) * (180 * Real.log (Real.log 180)) ≤ 1170 * (180 * (1647305 / 1000000)) := by gcongr
    _ < 546 * (360 * (1772594 / 1000000)) := by norm_num
    _ ≤ 546 * (360 * Real.log (Real.log 360)) := by gcongr


lemma wit420 : G 420 < G 84 := by
  have hs1 : ArithmeticFunction.sigma 1 420 = 1344 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 84 = 224 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1798446 : ℝ) / 1000000 ≤ Real.log (Real.log (420 : ℝ)) :=
    LL_ge _ ((6040254 : ℝ) / 1000000) _ 8 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (84 : ℝ)) ≤ (1488586 : ℝ) / 1000000 :=
    LL_le _ ((4430818 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (420 : ℝ) (by norm_num)
  have hp2 := LL_pos (84 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (1344 : ℝ) * (84 * Real.log (Real.log 84)) ≤ 1344 * (84 * (1488586 / 1000000)) := by gcongr
    _ < 224 * (420 * (1798446 / 1000000)) := by norm_num
    _ ≤ 224 * (420 * Real.log (Real.log 420)) := by gcongr


lemma wit720 : G 720 < G 360 := by
  have hs1 : ArithmeticFunction.sigma 1 720 = 2418 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 360 = 1170 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1883920 : ℝ) / 1000000 ≤ Real.log (Real.log (720 : ℝ)) :=
    LL_ge _ ((6579251 : ℝ) / 1000000) _ 9 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (360 : ℝ)) ≤ (1772596 : ℝ) / 1000000 :=
    LL_le _ ((5886106 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (720 : ℝ) (by norm_num)
  have hp2 := LL_pos (360 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (2418 : ℝ) * (360 * Real.log (Real.log 360)) ≤ 2418 * (360 * (1772596 / 1000000)) := by gcongr
    _ < 1170 * (720 * (1883920 / 1000000)) := by norm_num
    _ ≤ 1170 * (720 * Real.log (Real.log 720)) := by gcongr


lemma wit840 : G 840 < G 120 := by
  have hs1 : ArithmeticFunction.sigma 1 840 = 2880 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 120 = 360 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (1907080 : ℝ) / 1000000 ≤ Real.log (Real.log (840 : ℝ)) :=
    LL_ge _ ((6733401 : ℝ) / 1000000) _ 9 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (120 : ℝ)) ≤ (1566008 : ℝ) / 1000000 :=
    LL_le _ ((4787493 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (840 : ℝ) (by norm_num)
  have hp2 := LL_pos (120 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (2880 : ℝ) * (120 * Real.log (Real.log 120)) ≤ 2880 * (120 * (1566008 / 1000000)) := by gcongr
    _ < 360 * (840 * (1907080 / 1000000)) := by norm_num
    _ ≤ 360 * (840 * Real.log (Real.log 840)) := by gcongr


lemma wit2520 : G 2520 < G 360 := by
  have hs1 : ArithmeticFunction.sigma 1 2520 = 9360 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 360 = 1170 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (2058219 : ℝ) / 1000000 ≤ Real.log (Real.log (2520 : ℝ)) :=
    LL_ge _ ((7832014 : ℝ) / 1000000) _ 11 2 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (360 : ℝ)) ≤ (1772596 : ℝ) / 1000000 :=
    LL_le _ ((5886106 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (2520 : ℝ) (by norm_num)
  have hp2 := LL_pos (360 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (9360 : ℝ) * (360 * Real.log (Real.log 360)) ≤ 9360 * (360 * (1772596 / 1000000)) := by gcongr
    _ < 1170 * (2520 * (2058219 / 1000000)) := by norm_num
    _ ≤ 1170 * (2520 * Real.log (Real.log 2520)) := by gcongr


lemma wit5040 : G 5040 < G 2520 := by
  have hs1 : ArithmeticFunction.sigma 1 5040 = 19344 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hs2 : ArithmeticFunction.sigma 1 2520 = 9360 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  have hlo : (2143021 : ℝ) / 1000000 ≤ Real.log (Real.log (5040 : ℝ)) :=
    LL_ge _ ((8525161 : ℝ) / 1000000) _ 12 3 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hhi : Real.log (Real.log (2520 : ℝ)) ≤ (2058221 : ℝ) / 1000000 :=
    LL_le _ ((7832016 : ℝ) / 1000000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp1 := LL_pos (5040 : ℝ) (by norm_num)
  have hp2 := LL_pos (2520 : ℝ) (by norm_num)
  unfold G
  rw [hs1, hs2]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  calc (19344 : ℝ) * (2520 * Real.log (Real.log 2520)) ≤ 19344 * (2520 * (2058221 / 1000000)) := by gcongr
    _ < 9360 * (5040 * (2143021 / 1000000)) := by norm_num
    _ ≤ 9360 * (5040 * Real.log (Real.log 5040)) := by gcongr

end BRHExtra

namespace BRHExtra
open BRHGron

lemma G2_neg : G 2 < 0 := by
  have hl : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : Real.log (Real.log 2) < 0 := Real.log_neg hl0 hl
  unfold G
  have hs : ArithmeticFunction.sigma 1 2 = 3 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  rw [hs]; push_cast
  apply div_neg_of_pos_of_neg (by norm_num); nlinarith

lemma G4_ge : (4.4 : ℝ) ≤ G 4 := by
  have hhi : Real.log (Real.log (4 : ℝ)) ≤ (3267 : ℝ) / 10000 :=
    LL_le _ ((13863 : ℝ) / 10000) _ (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [expLower, Finset.sum_range_succ]) (by norm_num)
  have hp := LL_pos (4 : ℝ) (by norm_num)
  have hs : ArithmeticFunction.sigma 1 4 = 7 := by
    rw [sigma_eq_fast _ (by norm_num)]; decide +kernel
  unfold G; rw [hs]; push_cast
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma small_checked : ((List.range' 8 8).all fun n => decide (100 * fastSigma n ≤ 234 * n)) = true := by
  decide +kernel

lemma big_checked : ((List.range' 16 5025).all fun n => decide (100 * fastSigma n ≤ 384 * n)) = true := by
  decide +kernel

lemma Gm_le (m : ℕ) (h8 : 8 ≤ m) (h : m ≤ 5040) : G m ≤ 4 := by
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast h8
  have hp := LL_pos (m : ℝ) (by linarith)
  have hm0 : (0 : ℝ) < m := by linarith
  have hl8 : (732099 : ℝ) / 1000000 ≤ Real.log (Real.log (8 : ℝ)) :=
    LL_ge _ ((2079441 : ℝ) / 1000000) _ 3 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  have hl16 : (1019781 : ℝ) / 1000000 ≤ Real.log (Real.log (16 : ℝ)) :=
    LL_ge _ ((2772588 : ℝ) / 1000000) _ 4 1 (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ]) (by norm_num)
      (by norm_num [logLower, Finset.sum_range_succ])
  unfold G
  rw [div_le_iff₀ (by positivity)]
  rcases lt_or_ge m 16 with h16 | h16
  · have hmem : m ∈ List.range' 8 8 := List.mem_range'.mpr ⟨m - 8, by omega, by omega⟩
    have hc := List.all_eq_true.mp small_checked m hmem
    simp only [decide_eq_true_eq] at hc
    rw [← sigma_eq_fast m (by omega)] at hc
    have hc' : (100 : ℝ) * ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) ≤ 234 * m := by exact_mod_cast hc
    have hmono := LL_mono (show (3:ℝ) ≤ 8 by norm_num) hm8
    nlinarith
  · have hmem : m ∈ List.range' 16 5025 := List.mem_range'.mpr ⟨m - 16, by omega, by omega⟩
    have hc := List.all_eq_true.mp big_checked m hmem
    simp only [decide_eq_true_eq] at hc
    rw [← sigma_eq_fast m (by omega)] at hc
    have hc' : (100 : ℝ) * ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) ≤ 384 * m := by exact_mod_cast hc
    have h16r : (16 : ℝ) ≤ m := by exact_mod_cast h16
    have hmono := LL_mono (show (3:ℝ) ≤ 16 by norm_num) h16r
    nlinarith

end BRHExtra

open BRHGron BRHExtra in
theorem solution :
    let G (n : ℕ) : ℝ := ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))
    ∀ n : ℕ, ((1 < n ∧ ¬ n.Prime) ∧ (∀ p : ℕ, p.Prime → p ∣ n → G (n / p) ≤ G n) ∧ (∀ k : ℕ, 2 ≤ k → G (k*n) ≤ G n)) ↔ n = 4 := by
  intro G' n
  show ((1 < n ∧ ¬ n.Prime) ∧ (∀ p : ℕ, p.Prime → p ∣ n → BRHGron.G (n / p) ≤ BRHGron.G n) ∧
    (∀ k : ℕ, 2 ≤ k → BRHGron.G (k*n) ≤ BRHGron.G n)) ↔ n = 4
  constructor
  · rintro ⟨⟨h1, hnp⟩, hL, hR⟩
    by_contra h4
    have hGlt : BRHGron.G n < Real.exp Real.eulerMascheroniConstant := by
      rcases lt_or_ge 5040 n with h | h
      · exact G_lt n h
      · by_cases hE : n ∈ Elist
        · exfalso
          simp only [Elist, List.mem_cons, List.not_mem_nil, or_false] at hE
          rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hnp (by norm_num)
          · exact h4 rfl
          · exact hnp (by norm_num)
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 6 / 2 = 3 := by norm_num
            rw [e] at hw
            linarith [wit6]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 8 / 2 = 4 := by norm_num
            rw [e] at hw
            linarith [wit8]
          · have hw := hL 3 (by norm_num) (by norm_num)
            have e : 9 / 3 = 3 := by norm_num
            rw [e] at hw
            linarith [wit9]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 10 / 2 = 5 := by norm_num
            rw [e] at hw
            linarith [wit10]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 12 / 2 = 6 := by norm_num
            rw [e] at hw
            linarith [wit12]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 16 / 2 = 8 := by norm_num
            rw [e] at hw
            linarith [wit16]
          · have hw := hL 3 (by norm_num) (by norm_num)
            have e : 18 / 3 = 6 := by norm_num
            rw [e] at hw
            linarith [wit18]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 20 / 2 = 10 := by norm_num
            rw [e] at hw
            linarith [wit20]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 24 / 2 = 12 := by norm_num
            rw [e] at hw
            linarith [wit24]
          · have hw := hL 3 (by norm_num) (by norm_num)
            have e : 30 / 3 = 10 := by norm_num
            rw [e] at hw
            linarith [wit30]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 36 / 2 = 18 := by norm_num
            rw [e] at hw
            linarith [wit36]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 48 / 2 = 24 := by norm_num
            rw [e] at hw
            linarith [wit48]
          · have hw := hL 5 (by norm_num) (by norm_num)
            have e : 60 / 5 = 12 := by norm_num
            rw [e] at hw
            linarith [wit60]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 72 / 2 = 36 := by norm_num
            rw [e] at hw
            linarith [wit72]
          · have hw := hL 7 (by norm_num) (by norm_num)
            have e : 84 / 7 = 12 := by norm_num
            rw [e] at hw
            linarith [wit84]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 120 / 2 = 60 := by norm_num
            rw [e] at hw
            linarith [wit120]
          · have hw := hL 3 (by norm_num) (by norm_num)
            have e : 180 / 3 = 60 := by norm_num
            rw [e] at hw
            linarith [wit180]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 240 / 2 = 120 := by norm_num
            rw [e] at hw
            linarith [wit240]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 360 / 2 = 180 := by norm_num
            rw [e] at hw
            linarith [wit360]
          · have hw := hL 5 (by norm_num) (by norm_num)
            have e : 420 / 5 = 84 := by norm_num
            rw [e] at hw
            linarith [wit420]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 720 / 2 = 360 := by norm_num
            rw [e] at hw
            linarith [wit720]
          · have hw := hL 7 (by norm_num) (by norm_num)
            have e : 840 / 7 = 120 := by norm_num
            rw [e] at hw
            linarith [wit840]
          · have hw := hL 7 (by norm_num) (by norm_num)
            have e : 2520 / 7 = 360 := by norm_num
            rw [e] at hw
            linarith [wit2520]
          · have hw := hL 2 (by norm_num) (by norm_num)
            have e : 5040 / 2 = 2520 := by norm_num
            rw [e] at hw
            linarith [wit5040]
        · have h5 : 5 ≤ n := by
            by_contra hlt
            push_neg at hlt
            interval_cases n
            · exact hnp Nat.prime_two
            · exact hnp Nat.prime_three
            · exact h4 rfl
          rcases (show (5 ≤ n ∧ n < 7) ∨ (7 ≤ n ∧ n < 14) ∨ (14 ≤ n ∧ n < 28) ∨ (28 ≤ n ∧ n < 40) ∨ (40 ≤ n ∧ n < 80) ∨ (80 ≤ n ∧ n < 96) ∨ (96 ≤ n ∧ n < 144) ∨ (144 ≤ n ∧ n < 168) ∨ (168 ≤ n ∧ n < 336) ∨ (336 ≤ n ∧ n < 480) ∨ (480 ≤ n ∧ n < 1080) ∨ (1080 ≤ n ∧ n < 1260) ∨ (1260 ≤ n ∧ n < 1680) ∨ (1680 ≤ n ∧ n < 3360) ∨ (3360 ≤ n ∧ n < 5041) by omega) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          · exact iv0 n h.1 h.2 hE
          · exact iv1 n h.1 h.2 hE
          · exact iv2 n h.1 h.2 hE
          · exact iv3 n h.1 h.2 hE
          · exact iv4 n h.1 h.2 hE
          · exact iv5 n h.1 h.2 hE
          · exact iv6 n h.1 h.2 hE
          · exact iv7 n h.1 h.2 hE
          · exact iv8 n h.1 h.2 hE
          · exact iv9 n h.1 h.2 hE
          · exact iv10 n h.1 h.2 hE
          · exact iv11 n h.1 h.2 hE
          · exact iv12 n h.1 h.2 hE
          · exact iv13 n h.1 h.2 hE
          · exact iv14 n h.1 h.2 hE
    obtain ⟨k, hk2, -, hk⟩ := exists_mult n (by omega)
      (Real.exp Real.eulerMascheroniConstant - BRHGron.G n) (by linarith) 0
    have := hR k hk2
    linarith
  · rintro rfl
    refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · intro p hp hpd
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpd))
      subst hp2
      norm_num
      linarith [G2_neg, G4_ge]
    · intro k hk
      have := G4_ge
      rcases lt_or_ge 5040 (k*4) with h | h
      · linarith [G_lt (k*4) h, EG_lt_two]
      · linarith [Gm_le (k*4) (by omega) h]
