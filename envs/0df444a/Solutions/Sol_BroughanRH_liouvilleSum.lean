-- Prove2me | solution 1 for BroughanRH.liouvilleSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:41:51.990024+00:00
-- url     : https://prove2.me/submissions/79d17260-b41b-4923-8e4e-e67af6dbbbac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.Omega

namespace BRHMob

/-- `g = λ * ζ`, the indicator of the nonzero squares. -/
noncomputable def g : ArithmeticFunction ℤ := liouville * (ζ : ArithmeticFunction ℤ)

lemma g_mult : g.IsMultiplicative := isMultiplicative_liouville.mul isMultiplicative_zeta.natCast

lemma alt_sum (k : ℕ) : ∑ i ∈ range (k + 1), ((-1 : ℤ) ^ i) = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · have h1 : ¬ Even (k+1) := by rw [Nat.even_add_one]; exact not_not.2 h
      simp [h, h1, pow_succ, h.neg_one_pow]
    · have h1 : Even (k+1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.2 h
      have h2 : ¬ Even k := Nat.not_even_iff_odd.2 h
      simp [h1, h2, pow_succ, h.neg_one_pow]

lemma g_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : g (p ^ k) = if Even k then 1 else 0 := by
  rw [g, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, ← alt_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]

lemma g_zero_or_one (n : ℕ) : g n = 0 ∨ g n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [g_mult.multiplicative_factorization g hn, Finsupp.prod]
  refine Finset.prod_induction _ (fun x => x = 0 ∨ x = 1) ?_ (Or.inr rfl) ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  · intro p hp
    rw [g_prime_pow (Nat.prime_of_mem_primeFactors (by simpa using hp))]
    split_ifs <;> simp

lemma isSquare_of_g_ne_zero {n : ℕ} (h : g n ≠ 0) : ∃ m, n = m ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨0, rfl⟩
  have hev : ∀ p ∈ n.factorization.support, Even (n.factorization p) := by
    intro p hp
    by_contra hodd
    apply h
    rw [g_mult.multiplicative_factorization g hn, Finsupp.prod]
    refine Finset.prod_eq_zero hp ?_
    rw [g_prime_pow (Nat.prime_of_mem_primeFactors (by simpa using hp)), if_neg hodd]
  refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 (hev p hp))]

lemma liouville_eq : (liouville : ArithmeticFunction ℤ) = g * μ := by
  rw [g, mul_assoc, coe_zeta_mul_moebius, mul_one]

lemma liouville_sum_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, liouville n = ∑ a ∈ Ioc 0 N, g a * ∑ b ∈ Ioc 0 (N / a), μ b := by
  rw [liouville_eq, sum_Ioc_mul_eq_sum_sum]

lemma Icc_one_eq (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext x; simp only [mem_Icc, mem_Ioc]; omega

/-- A global Mertens bound from the eventual one. -/
lemma mertens_global {s : ℝ} (hs : 0 < s)
    (hM : Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, |∑ b ∈ Ioc 0 x, ((μ b : ℤ) : ℝ)| ≤ C * (x : ℝ) ^ s := by
  obtain ⟨c, hc⟩ := hM.bound
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hc
  refine ⟨|c| + N0, by positivity, fun x => ?_⟩
  have hxs : 0 ≤ (x : ℝ) ^ s := by positivity
  by_cases hx : N0 ≤ x
  · have h := hN0 x hx
    have hc' : (((∑ b ∈ Ioc 0 x, ((μ b : ℤ) : ℝ)) : ℝ) : ℂ)
        = ∑ n ∈ Finset.Icc 1 x, ((μ n : ℤ) : ℂ) := by rw [Icc_one_eq]; push_cast; rfl
    rw [← hc', Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxs] at h
    calc _ ≤ c * (x : ℝ) ^ s := h
      _ ≤ |c| * (x : ℝ) ^ s := by gcongr; exact le_abs_self c
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) N0]
  · have h1 : |∑ b ∈ Ioc 0 x, ((μ b : ℤ) : ℝ)| ≤ x := by
      calc _ ≤ ∑ b ∈ Ioc 0 x, |((μ b : ℤ) : ℝ)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ b ∈ Ioc 0 x, (1 : ℝ) := by
          refine sum_le_sum fun b _ => ?_
          rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
        _ = x := by simp
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · simp [Real.zero_rpow hs.ne']
    have h2 : (1 : ℝ) ≤ (x : ℝ) ^ s := Real.one_le_rpow (by exact_mod_cast hpos) hs.le
    have h3 : (x : ℝ) ≤ N0 := by exact_mod_cast (not_le.1 hx).le
    nlinarith [abs_nonneg c]

lemma sum_g_le {s : ℝ} (hs : 1 / 2 < s) (N : ℕ) :
    ∑ a ∈ Ioc 0 N, |((g a : ℤ) : ℝ)| * ((a : ℝ) ^ s)⁻¹
      ≤ ∑' m : ℕ, ((m : ℝ) ^ (2 * s))⁻¹ := by
  have hsum : Summable (fun m : ℕ => ((m : ℝ) ^ (2 * s))⁻¹) :=
    Real.summable_nat_rpow_inv.2 (by linarith)
  have e1 : ∑ a ∈ Ioc 0 N, |((g a : ℤ) : ℝ)| * ((a : ℝ) ^ s)⁻¹
      = ∑ a ∈ (Ioc 0 N).filter (fun a => g a ≠ 0), ((a : ℝ) ^ s)⁻¹ := by
    rw [sum_filter]
    refine sum_congr rfl fun a _ => ?_
    rcases g_zero_or_one a with h | h <;> simp [h]
  have hsub : (Ioc 0 N).filter (fun a => g a ≠ 0) ⊆ (Ioc 0 N).image (fun m => m ^ 2) := by
    intro a ha
    rw [mem_filter, mem_Ioc] at ha
    obtain ⟨m, rfl⟩ := isSquare_of_g_ne_zero ha.2
    rw [mem_image]
    refine ⟨m, ?_, rfl⟩
    rw [mem_Ioc]
    have : m ≤ m ^ 2 := by nlinarith [Nat.le_self_pow two_ne_zero m]
    refine ⟨?_, this.trans ha.1.2⟩
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at ha
    · exact h
  rw [e1]
  calc _ ≤ ∑ a ∈ (Ioc 0 N).image (fun m : ℕ => m ^ 2), (((a : ℕ) : ℝ) ^ s)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ m ∈ Ioc 0 N, (((m ^ 2 : ℕ) : ℝ) ^ s)⁻¹ := by
        rw [sum_image]
        intro x _ y _ hxy
        exact Nat.pow_left_injective two_ne_zero hxy
    _ = ∑ m ∈ Ioc 0 N, ((m : ℝ) ^ (2 * s))⁻¹ := by
        refine sum_congr rfl fun m _ => ?_
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
        norm_num
    _ ≤ _ := hsum.sum_le_tsum _ (fun _ _ => by positivity)

lemma liouville_bound {s : ℝ} (hs : 1 / 2 < s)
    (hM : Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ s)) :
    ∃ K : ℝ, ∀ N : ℕ, |∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)| ≤ K * (N : ℝ) ^ s := by
  have hs0 : 0 < s := by linarith
  obtain ⟨C, hC0, hC⟩ := mertens_global hs0 hM
  set Z := ∑' m : ℕ, ((m : ℝ) ^ (2 * s))⁻¹
  refine ⟨C * Z, fun N => ?_⟩
  have hid : ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)
      = ∑ a ∈ Ioc 0 N, ((g a : ℤ) : ℝ) * ∑ b ∈ Ioc 0 (N / a), ((μ b : ℤ) : ℝ) := by
    rw [Icc_one_eq]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (liouville_sum_eq N)
  rw [hid]
  have hNs : 0 ≤ (N : ℝ) ^ s := by positivity
  calc _ ≤ ∑ a ∈ Ioc 0 N, |((g a : ℤ) : ℝ) * ∑ b ∈ Ioc 0 (N / a), ((μ b : ℤ) : ℝ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Ioc 0 N, |((g a : ℤ) : ℝ)| * (C * ((N : ℝ) ^ s * ((a : ℝ) ^ s)⁻¹)) := by
        refine sum_le_sum fun a ha => ?_
        rw [abs_mul]
        gcongr
        have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Ioc.1 ha).1
        calc _ ≤ C * (((N / a : ℕ) : ℝ)) ^ s := hC _
          _ ≤ C * ((N : ℝ) / a) ^ s := by
              gcongr
              exact Nat.cast_div_le
          _ = _ := by rw [Real.div_rpow (Nat.cast_nonneg _) ha0.le, div_eq_mul_inv]
    _ = C * (N : ℝ) ^ s * ∑ a ∈ Ioc 0 N, |((g a : ℤ) : ℝ)| * ((a : ℝ) ^ s)⁻¹ := by
        rw [mul_sum]; refine sum_congr rfl fun a _ => by ring
    _ ≤ C * (N : ℝ) ^ s * Z := by gcongr; exact sum_g_le hs N
    _ = _ := by ring

end BRHMob

open BRHMob in
theorem solution :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)) (fun N : ℕ => (N : ℝ) ^ (1/2 + ε)) := by
  intro ε hε
  obtain ⟨K, hK⟩ := liouville_bound (by linarith)
    (moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis ε hε)
  refine Asymptotics.IsBigO.of_bound K (Filter.Eventually.of_forall fun N => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N : ℝ) ^ (1/2 + ε))]
  exact hK N
