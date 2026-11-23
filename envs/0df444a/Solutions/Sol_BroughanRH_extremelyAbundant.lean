-- Prove2me | solution 1 for BroughanRH.extremelyAbundant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:57:01.388141+00:00
-- url     : https://prove2.me/submissions/6f4581a9-f6c6-4bde-8a10-a3c239b31889
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

open BRHGron in
theorem solution :
    let G (n : ℕ) : ℝ := ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))
    Set.Infinite {n : ℕ | 10080 ≤ n ∧ ∀ m : ℕ, 10080 ≤ m → m < n → G m < G n} := by
  intro G'
  show Set.Infinite {n : ℕ | 10080 ≤ n ∧ ∀ m : ℕ, 10080 ≤ m → m < n → BRHGron.G m < BRHGron.G n}
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  set N := max B 10080 with hN
  have hne : (Finset.Icc 10080 N).Nonempty := ⟨10080, by simp [hN]⟩
  set M := (Finset.Icc 10080 N).sup' hne BRHGron.G with hM
  have hMlt : M < Real.exp Real.eulerMascheroniConstant := by
    rw [hM, Finset.sup'_lt_iff]
    intro m hm
    exact G_lt m (by simp at hm; omega)
  obtain ⟨k, -, hkN, hk⟩ := exists_mult 1 one_pos
    (Real.exp Real.eulerMascheroniConstant - M) (by linarith) (N + 1)
  rw [mul_one] at hk
  have hex : ∃ m, 10080 ≤ m ∧ M < BRHGron.G m := ⟨k, by omega, by linarith⟩
  classical
  set n := Nat.find hex with hn
  have hnspec := Nat.find_spec hex
  have hnN : N < n := by
    by_contra hle
    push_neg at hle
    have : BRHGron.G n ≤ M := Finset.le_sup' BRHGron.G (by simp; exact ⟨hnspec.1, hle⟩)
    linarith [hnspec.2]
  have hmem : n ∈ {n : ℕ | 10080 ≤ n ∧ ∀ m : ℕ, 10080 ≤ m → m < n → BRHGron.G m < BRHGron.G n} := by
    refine ⟨hnspec.1, fun m hm hmn => ?_⟩
    have hmin := Nat.find_min hex hmn
    push_neg at hmin
    linarith [hmin hm, hnspec.2]
  have := hB hmem
  omega
