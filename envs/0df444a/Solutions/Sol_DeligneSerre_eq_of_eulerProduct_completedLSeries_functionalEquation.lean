-- Prove2me | solution 1 for DeligneSerre.eq_of_eulerProduct_completedLSeries_functionalEquation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7e4d1219-de37-541f-9b58-6368a2dcb577

import Mathlib
import Theorems.Thm_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_eq_of_eulerProduct_completedLSeries_functionalEquation

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open Polynomial Complex
open scoped LSeries.notation ArithmeticFunction

namespace DeligneSerreCmp

section Arith

variable (S : Finset ℕ) (R : ℕ → ℂ[X])

def corr (n : ℕ) : ℂ :=
  if n ≠ 0 ∧ n.primeFactors ⊆ S then ∏ p ∈ S, (R p).coeff (n.factorization p) else 0

variable {S R}

theorem corr_zero : corr S R 0 = 0 := by simp [corr]

theorem corr_one (h0 : ∀ p ∈ S, (R p).coeff 0 = 1) : corr S R 1 = 1 := by
  simp only [corr, ne_eq, one_ne_zero, not_false_eq_true, Nat.primeFactors_one,
    Finset.empty_subset, and_self, ↓reduceIte, Nat.factorization_one, Finsupp.coe_zero,
    Pi.zero_apply]
  exact Finset.prod_eq_one fun p hp => h0 p hp

theorem corr_of_not_subset {n : ℕ} (h : ¬ n.primeFactors ⊆ S) : corr S R n = 0 := by
  simp [corr, h]

theorem corr_of_subset {n : ℕ} (hn : n ≠ 0) (h : n.primeFactors ⊆ S) :
    corr S R n = ∏ p ∈ S, (R p).coeff (n.factorization p) := by
  simp [corr, hn, h]

theorem corr_prime_pow_of_mem (h0 : ∀ p ∈ S, (R p).coeff 0 = 1) {p : ℕ} (hp : p.Prime)
    (hpS : p ∈ S) (k : ℕ) : corr S R (p ^ k) = (R p).coeff k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, corr_one h0, h0 p hpS]
  rw [corr_of_subset (pow_ne_zero k hp.ne_zero)]
  · rw [Finset.prod_eq_single p]
    · rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    · intro q _ hqp
      rw [Nat.Prime.factorization_pow hp, Finsupp.single_apply, if_neg (Ne.symm hqp), h0 q ‹_›]
    · intro h; exact absurd hpS h
  · rw [Nat.primeFactors_prime_pow hk.ne' hp]
    exact Finset.singleton_subset_iff.mpr hpS

theorem corr_prime_pow_of_not_mem {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) {k : ℕ} (hk : k ≠ 0) :
    corr S R (p ^ k) = 0 := by
  apply corr_of_not_subset
  rw [Nat.primeFactors_prime_pow hk hp, Finset.singleton_subset_iff]
  exact hpS

theorem corr_mul_of_coprime (h0 : ∀ p ∈ S, (R p).coeff 0 = 1) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hmn : m.Coprime n) : corr S R (m * n) = corr S R m * corr S R n := by
  have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors := Nat.primeFactors_mul hm hn
  by_cases hsub : (m * n).primeFactors ⊆ S
  · have hmS : m.primeFactors ⊆ S := (Finset.subset_union_left.trans (hpf ▸ hsub))
    have hnS : n.primeFactors ⊆ S := (Finset.subset_union_right.trans (hpf ▸ hsub))
    rw [corr_of_subset (mul_ne_zero hm hn) hsub, corr_of_subset hm hmS, corr_of_subset hn hnS,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply]

    rcases Nat.eq_zero_or_pos (m.factorization p) with h1 | h1
    · rw [h1, zero_add, h0 p hp, one_mul]
    · have h2 : n.factorization p = 0 := by
        by_contra h2
        have hpm : p ∈ m.primeFactors := Nat.support_factorization m ▸ Finsupp.mem_support_iff.mpr h1.ne'
        have hpn : p ∈ n.primeFactors := Nat.support_factorization n ▸ Finsupp.mem_support_iff.mpr h2
        exact Finset.disjoint_left.mp hmn.disjoint_primeFactors hpm hpn
      rw [h2, add_zero, h0 p hp, mul_one]
  · rw [corr_of_not_subset hsub]
    rw [hpf, Finset.union_subset_iff, not_and_or] at hsub
    rcases hsub with h | h
    · rw [corr_of_not_subset h, zero_mul]
    · rw [corr_of_not_subset h, mul_zero]

theorem isMultiplicative_toArithmeticFunction {f : ℕ → ℂ} (h1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m * f n) :
    (toArithmeticFunction f).IsMultiplicative := by
  refine ⟨by simp [toArithmeticFunction, h1], fun {m n} hmn => ?_⟩
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, mul_eq_zero]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg (not_or.mpr ⟨hm, hn⟩), if_neg hm, if_neg hn]
  exact hmul m n hm hn hmn

theorem convolution_prime_pow (f g : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f ⍟ g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [LSeries.convolution_def]
  simp only
  rw [Nat.sum_divisorsAntidiagonal (fun x y => f x * g y), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

theorem sum_antidiagonal_of_mul_mk_eq_one {f : ℕ → ℂ} {p : ℕ} {Rp : ℂ[X]}
    (h : (Rp : PowerSeries ℂ) * PowerSeries.mk (fun k => f (p ^ k)) = 1) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), f (p ^ i) * Rp.coeff (k - i) = if k = 0 then 1 else 0 := by
  have hk := congrArg (PowerSeries.coeff k) h
  rw [mul_comm, PowerSeries.coeff_mul, PowerSeries.coeff_one] at hk
  rw [← hk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe]

theorem coeff_zero_eq_one_of_mul_mk_eq_one {f : ℕ → ℂ} (h1 : f 1 = 1) {p : ℕ} {Rp : ℂ[X]}
    (h : (Rp : PowerSeries ℂ) * PowerSeries.mk (fun k => f (p ^ k)) = 1) : Rp.coeff 0 = 1 := by
  have := sum_antidiagonal_of_mul_mk_eq_one h 0
  simpa [h1] using this

theorem eq_on_prime_pow_of_eq {f g : ℕ → ℂ} {p : ℕ} {Rp : ℂ[X]}
    (hf : (Rp : PowerSeries ℂ) * PowerSeries.mk (fun k => f (p ^ k)) = 1)
    (hg : (Rp : PowerSeries ℂ) * PowerSeries.mk (fun k => g (p ^ k)) = 1) (k : ℕ) :
    f (p ^ k) = g (p ^ k) := by
  have hR : PowerSeries.constantCoeff (Rp : PowerSeries ℂ) ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff hf
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have h1 : PowerSeries.mk (fun k => f (p ^ k)) = (Rp : PowerSeries ℂ)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one hR, mul_comm]; exact hf
  have h2 : PowerSeries.mk (fun k => g (p ^ k)) = (Rp : PowerSeries ℂ)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one hR, mul_comm]; exact hg
  have := congrArg (PowerSeries.coeff k) (h1.trans h2.symm)
  simpa using this

end Arith

section Conv

variable {S : Finset ℕ} {a b : ℕ → ℂ} {P Q : ℕ → ℂ[X]}

theorem convolution_corr_prime_pow (hS : ∀ p ∈ S, p.Prime) (ha₁ : a 1 = 1)
    (hP : ∀ p : ℕ, p.Prime → (P p : PowerSeries ℂ) * PowerSeries.mk (fun k => a (p ^ k)) = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (a ⍟ corr S P) (p ^ k) = if p ∈ S then (if k = 0 then 1 else 0) else a (p ^ k) := by
  have h0 : ∀ q ∈ S, (P q).coeff 0 = 1 := fun q hq =>
    coeff_zero_eq_one_of_mul_mk_eq_one ha₁ (hP q (hS q hq))
  rw [convolution_prime_pow a (corr S P) hp k]
  by_cases hpS : p ∈ S
  · rw [if_pos hpS, ← sum_antidiagonal_of_mul_mk_eq_one (hP p hp) k]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [corr_prime_pow_of_mem h0 hp hpS]
  · rw [if_neg hpS, Finset.sum_eq_single k]
    · rw [Nat.sub_self, pow_zero, corr_one h0, mul_one]
    · intro i hi hik
      have hlt : i < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hik
      rw [corr_prime_pow_of_not_mem hp hpS (by omega), mul_zero]
    · intro h; exact absurd (Finset.self_mem_range_succ k) h

theorem convolution_corr_eq (hS : ∀ p ∈ S, p.Prime) (ha₁ : a 1 = 1) (hb₁ : b 1 = 1)
    (hamul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hbmul : ∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n)
    (hP : ∀ p : ℕ, p.Prime → (P p : PowerSeries ℂ) * PowerSeries.mk (fun k => a (p ^ k)) = 1)
    (hQ : ∀ p : ℕ, p.Prime → (Q p : PowerSeries ℂ) * PowerSeries.mk (fun k => b (p ^ k)) = 1)
    (hPQ : ∀ p : ℕ, p.Prime → p ∉ S → P p = Q p) :
    a ⍟ corr S P = b ⍟ corr S Q := by
  have hP0 : ∀ q ∈ S, (P q).coeff 0 = 1 := fun q hq =>
    coeff_zero_eq_one_of_mul_mk_eq_one ha₁ (hP q (hS q hq))
  have hQ0 : ∀ q ∈ S, (Q q).coeff 0 = 1 := fun q hq =>
    coeff_zero_eq_one_of_mul_mk_eq_one hb₁ (hQ q (hS q hq))
  have hA : (toArithmeticFunction a).IsMultiplicative :=
    isMultiplicative_toArithmeticFunction ha₁ fun m n _ _ h => hamul m n h
  have hB : (toArithmeticFunction b).IsMultiplicative :=
    isMultiplicative_toArithmeticFunction hb₁ fun m n _ _ h => hbmul m n h
  have hCP : (toArithmeticFunction (corr S P)).IsMultiplicative :=
    isMultiplicative_toArithmeticFunction (corr_one hP0) fun m n hm hn h =>
      corr_mul_of_coprime hP0 hm hn h
  have hCQ : (toArithmeticFunction (corr S Q)).IsMultiplicative :=
    isMultiplicative_toArithmeticFunction (corr_one hQ0) fun m n hm hn h =>
      corr_mul_of_coprime hQ0 hm hn h
  have heq : toArithmeticFunction a * toArithmeticFunction (corr S P) =
      toArithmeticFunction b * toArithmeticFunction (corr S Q) := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hA.mul hCP) _ (hB.mul hCQ)]
    intro p k hp
    have h1 : (toArithmeticFunction a * toArithmeticFunction (corr S P)) (p ^ k) =
        (a ⍟ corr S P) (p ^ k) := rfl
    have h2 : (toArithmeticFunction b * toArithmeticFunction (corr S Q)) (p ^ k) =
        (b ⍟ corr S Q) (p ^ k) := rfl
    rw [h1, h2, convolution_corr_prime_pow hS ha₁ hP hp, convolution_corr_prime_pow hS hb₁ hQ hp]
    by_cases hpS : p ∈ S
    · rw [if_pos hpS, if_pos hpS]
    · rw [if_neg hpS, if_neg hpS]
      have hPQp := hPQ p hp hpS
      exact eq_on_prime_pow_of_eq (hP p hp) (by rw [hPQp]; exact hQ p hp) k
  show ⇑(toArithmeticFunction a * toArithmeticFunction (corr S P)) =
    ⇑(toArithmeticFunction b * toArithmeticFunction (corr S Q))
  rw [heq]

end Conv

section FiniteEuler

variable {S : Finset ℕ}

def nOf (S : Finset ℕ) (m : S → ℕ) : ℕ := ∏ p : S, (p : ℕ) ^ (m p)

theorem nOf_ne_zero (hS : ∀ p ∈ S, p.Prime) (m : S → ℕ) : nOf S m ≠ 0 := by
  unfold nOf
  rw [Finset.prod_ne_zero_iff]
  intro p _
  exact pow_ne_zero _ (hS p.1 p.2).ne_zero

theorem factorization_nOf (hS : ∀ p ∈ S, p.Prime) (m : S → ℕ) (p : S) :
    (nOf S m).factorization p = m p := by
  unfold nOf
  rw [Nat.factorization_prod fun (q : S) _ => pow_ne_zero _ (hS q.1 q.2).ne_zero]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Nat.factorization_pow,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · rw [(hS p.1 p.2).factorization_self, mul_one]
  · intro q _ hqp
    rw [Nat.Prime.factorization (hS q.1 q.2), Finsupp.single_apply, if_neg, mul_zero]
    intro h
    exact hqp (Subtype.ext h)
  · intro h; exact absurd (Finset.mem_univ p) h

theorem factorization_nOf_of_not_mem (hS : ∀ p ∈ S, p.Prime) (m : S → ℕ) {q : ℕ}
    (hq : q ∉ S) : (nOf S m).factorization q = 0 := by
  unfold nOf
  rw [Nat.factorization_prod fun (p : S) _ => pow_ne_zero _ (hS p.1 p.2).ne_zero]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Nat.factorization_pow,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Nat.Prime.factorization (hS p.1 p.2), Finsupp.single_apply, if_neg, mul_zero]
  intro h; exact hq (h ▸ p.2)

theorem primeFactors_nOf_subset (hS : ∀ p ∈ S, p.Prime) (m : S → ℕ) :
    (nOf S m).primeFactors ⊆ S := by
  intro q hq
  by_contra hqS
  have h := factorization_nOf_of_not_mem hS m hqS
  rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hq
  exact hq h

theorem nOf_injective (hS : ∀ p ∈ S, p.Prime) : Function.Injective (nOf S) := by
  intro m m' h
  funext p
  rw [← factorization_nOf hS m p, ← factorization_nOf hS m' p, h]

theorem natCast_pow_cpow (n k : ℕ) (z : ℂ) :
    (((n ^ k : ℕ)) : ℂ) ^ z = (((n : ℕ) : ℂ) ^ z) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

theorem natCast_prod_cpow {ι : Type*} (T : Finset ι) (c : ι → ℕ) (z : ℂ) :
    (((∏ i ∈ T, c i : ℕ)) : ℂ) ^ z = ∏ i ∈ T, ((c i : ℕ) : ℂ) ^ z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

theorem eq_nOf_of_subset (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : n ≠ 0) (h : n.primeFactors ⊆ S) :
    n = nOf S (fun p => n.factorization p) := by
  apply Nat.eq_of_factorization_eq hn (nOf_ne_zero hS _)
  intro q
  by_cases hqS : q ∈ S
  · rw [factorization_nOf hS _ ⟨q, hqS⟩]
  · rw [factorization_nOf_of_not_mem hS _ hqS]
    by_contra hne
    have : q ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      exact fun h0 => hne (h0 ▸ rfl) |>.elim
    exact hqS (h this)

variable (S) in

def eulerProd (R : ℕ → ℂ[X]) (s : ℂ) : ℂ := ∏ p ∈ S, (R p).eval ((p : ℂ) ^ (-s))

theorem LSeries_corr (hS : ∀ p ∈ S, p.Prime) (R : ℕ → ℂ[X]) (s : ℂ) :
    LSeries (corr S R) s = eulerProd S R s := by
  classical

  set d : S → ℕ := fun p => (R p).natDegree with hd
  set Box : Finset (S → ℕ) := Fintype.piFinset fun p : S => Finset.range (d p + 1) with hBox

  have hsupp : ∀ n : ℕ, n ∉ Box.image (nOf S) → LSeries.term (corr S R) s n = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · exact LSeries.term_zero _ _
    rw [LSeries.term_of_ne_zero hn0]
    suffices corr S R n = 0 by rw [this, zero_div]
    by_cases hsub : n.primeFactors ⊆ S
    · rw [corr_of_subset hn0 hsub]

      by_contra hne
      have hne' : ∀ p ∈ S, (R p).coeff (n.factorization p) ≠ 0 := fun p hp h0 =>
        hne (Finset.prod_eq_zero hp h0)
      apply hn
      refine Finset.mem_image.mpr ⟨fun p => n.factorization p, ?_, (eq_nOf_of_subset hS hn0 hsub).symm⟩
      rw [hBox, Fintype.mem_piFinset]
      intro p
      rw [Finset.mem_range, Nat.lt_succ_iff]
      by_contra hlt
      exact hne' p p.2 (Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hlt))
    · exact corr_of_not_subset hsub
  rw [LSeries, tsum_eq_sum (s := Box.image (nOf S)) hsupp,
    Finset.sum_image fun m _ m' _ h => nOf_injective hS h]

  have hexp : eulerProd S R s =
      ∑ m ∈ Box, ∏ p : S, (R p).coeff (m p) * (((p : ℕ) : ℂ) ^ (-s)) ^ (m p) := by
    rw [eulerProd, ← Finset.prod_coe_sort S, hBox,
      ← Finset.prod_univ_sum (fun p : S => Finset.range (d p + 1))
        (fun (p : S) (j : ℕ) => (R p).coeff j * (((p : ℕ) : ℂ) ^ (-s)) ^ j)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Polynomial.eval_eq_sum_range]
  rw [hexp]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [LSeries.term_of_ne_zero (nOf_ne_zero hS m),
    corr_of_subset (nOf_ne_zero hS m) (primeFactors_nOf_subset hS m), Finset.prod_mul_distrib,
    div_eq_mul_inv, ← Complex.cpow_neg]
  congr 1
  · rw [← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [factorization_nOf hS m p]
  · unfold nOf
    rw [natCast_prod_cpow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [natCast_pow_cpow]

theorem LSeriesSummable_corr (hS : ∀ p ∈ S, p.Prime) (R : ℕ → ℂ[X]) (s : ℂ) :
    LSeriesSummable (corr S R) s := by
  classical
  set d : S → ℕ := fun p => (R p).natDegree with hd
  set Box : Finset (S → ℕ) := Fintype.piFinset fun p : S => Finset.range (d p + 1) with hBox
  refine summable_of_ne_finset_zero (s := Box.image (nOf S)) fun n hn => ?_
  rcases eq_or_ne n 0 with rfl | hn0
  · exact LSeries.term_zero _ _
  rw [LSeries.term_of_ne_zero hn0]
  suffices corr S R n = 0 by rw [this, zero_div]
  by_cases hsub : n.primeFactors ⊆ S
  · rw [corr_of_subset hn0 hsub]
    by_contra hne
    have hne' : ∀ p ∈ S, (R p).coeff (n.factorization p) ≠ 0 := fun p hp h0 =>
      hne (Finset.prod_eq_zero hp h0)
    apply hn
    refine Finset.mem_image.mpr ⟨fun p => n.factorization p, ?_, (eq_nOf_of_subset hS hn0 hsub).symm⟩
    rw [hBox, Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range, Nat.lt_succ_iff]
    by_contra hlt
    exact hne' p p.2 (Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hlt))
  · exact corr_of_not_subset hsub

theorem differentiable_eulerProd (hS : ∀ p ∈ S, p.Prime) (R : ℕ → ℂ[X]) :
    Differentiable ℂ (eulerProd S R) := by
  have h : ∀ p ∈ S, Differentiable ℂ (fun s : ℂ => (R p).eval ((p : ℂ) ^ (-s))) := by
    intro p hp
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
    exact (R p).differentiable.comp ((differentiable_id.neg).const_cpow (Or.inl hp0))
  have := Differentiable.finsetProd (u := S) (f := fun p (s : ℂ) => (R p).eval ((p : ℂ) ^ (-s))) h
  have heq : eulerProd S R = ∏ i ∈ S, fun (s : ℂ) => (R i).eval ((i : ℂ) ^ (-s)) := by
    funext s
    simp [eulerProd, Finset.prod_apply]
  rw [heq]; exact this

end FiniteEuler

section Analytic

theorem eq_of_eq_on_real_gt {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (σ : ℝ) (h : ∀ s : ℝ, σ < s → f s = g s) : f = g := by
  set D : ℂ → ℂ := fun z => f z - g z with hD
  have hDa : AnalyticOnNhd ℂ D Set.univ := (hf.sub hg).differentiableOn.analyticOnNhd isOpen_univ
  set z₀ : ℂ := ((σ + 1 : ℝ) : ℂ) with hz₀

  have hloc : ∀ᶠ z in nhds z₀, D z = 0 := by
    rcases (hDa z₀ (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exact h0
    · exfalso
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
      obtain ⟨ε, hε, hball⟩ := hne
      have hz : dist (((σ + 1 + ε / 2 : ℝ)) : ℂ) z₀ < ε := by
        rw [hz₀, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [show σ + 1 + ε / 2 - (σ + 1) = ε / 2 by ring, abs_of_pos (by positivity)]
        linarith
      have hne' : (((σ + 1 + ε / 2 : ℝ)) : ℂ) ≠ z₀ := by
        rw [hz₀, Ne, Complex.ofReal_inj]
        linarith
      have := hball hz hne'
      apply this
      simp only [hD]
      rw [h _ (by linarith), sub_self]
  have hzero := hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₀) hloc
  funext z
  have := hzero (Set.mem_univ z)
  simpa [hD, sub_eq_zero] using this

theorem conj_ofReal_cpow_ofReal {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    starRingEnd ℂ ((x : ℂ) ^ (t : ℂ)) = (x : ℂ) ^ (t : ℂ) := by
  rw [← Complex.ofReal_cpow hx, Complex.conj_ofReal]

theorem conj_LSeries_ofReal (f : ℕ → ℂ) (s : ℝ) :
    starRingEnd ℂ (LSeries f s) = LSeries (fun m => starRingEnd ℂ (f m)) s := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀]
  congr 1
  have : ((n : ℂ)) = ((n : ℝ) : ℂ) := by norm_cast
  rw [this, conj_ofReal_cpow_ofReal (Nat.cast_nonneg n)]

theorem conj_eulerProd_ofReal (S : Finset ℕ) (R : ℕ → ℂ[X]) (s : ℝ) :
    starRingEnd ℂ (eulerProd S R s) = eulerProd S (fun p => (R p).map (starRingEnd ℂ)) s := by
  rw [eulerProd, eulerProd, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hx : starRingEnd ℂ (((p : ℕ) : ℂ) ^ (-(s : ℂ))) = ((p : ℕ) : ℂ) ^ (-(s : ℂ)) := by
    have : ((p : ℂ)) = ((p : ℝ) : ℂ) := by norm_cast
    rw [this, ← Complex.ofReal_neg, conj_ofReal_cpow_ofReal (Nat.cast_nonneg p)]
  rw [Polynomial.eval_map, ← hx, Polynomial.eval₂_hom, hx]

theorem LSeriesSummable_conj {f : ℕ → ℂ} {s : ℝ} (h : LSeriesSummable f s) :
    LSeriesSummable (fun m => starRingEnd ℂ (f m)) s := by
  rw [LSeriesSummable] at h ⊢
  rw [← summable_norm_iff] at h ⊢
  refine h.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div, RCLike.norm_conj]

theorem exists_LSeries_ne_zero {f : ℕ → ℂ} (h1 : f 1 = 1) {s₀ : ℝ} (hs : LSeriesSummable f s₀) :
    ∃ σ : ℝ, ∀ s : ℝ, σ < s → LSeries f s ≠ 0 := by
  set f' : ℕ → ℂ := fun m => if m = 0 then 0 else f m with hf'
  have hcongr : ∀ s : ℂ, LSeries f' s = LSeries f s := fun s =>
    LSeries_congr (fun {n} hn => by simp [hf', hn]) s
  have habs : LSeries.abscissaOfAbsConv f' < ⊤ := by
    have hs' : LSeriesSummable f' s₀ :=
      (LSeriesSummable_congr s₀ fun {n} hn => by simp [hf', hn]).mpr hs
    exact lt_of_le_of_lt hs'.abscissaOfAbsConv_le (EReal.coe_lt_top _)
  have ht := LSeries.tendsto_cpow_mul_atTop (f := f') (n := 0) (fun m hm => by
    simp [hf', Nat.le_zero.mp hm]) habs
  simp only [Nat.cast_zero, zero_add, one_cpow, one_mul] at ht
  have hf'1 : f' 1 = 1 := by simp [hf', h1]
  rw [hf'1] at ht

  have hev : ∀ᶠ x : ℝ in Filter.atTop, dist (LSeries f' x) 1 < 1 / 2 :=
    ht (Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨σ, hσ⟩ := Filter.eventually_atTop.mp hev
  refine ⟨σ, fun s hs h0 => ?_⟩
  have := hσ s hs.le
  rw [hcongr, h0, dist_zero_left, norm_one] at this
  norm_num at this

end Analytic

section Powers

variable {S : Finset ℕ}

theorem cpow_nOf (m : S → ℕ) (z : ℂ) :
    ((nOf S m : ℕ) : ℂ) ^ z = ∏ p : S, ((((p : ℕ) : ℂ)) ^ z) ^ (m p) := by
  unfold nOf
  rw [natCast_prod_cpow]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [natCast_pow_cpow]

theorem natCast_cpow_eq_prod (hS : ∀ p ∈ S, p.Prime) {M : ℕ} (hM : M ≠ 0)
    (hMS : M.primeFactors ⊆ S) (z : ℂ) :
    ((M : ℕ) : ℂ) ^ z = ∏ p ∈ S, ((((p : ℕ) : ℂ)) ^ z) ^ (M.factorization p) := by
  conv_lhs => rw [eq_nOf_of_subset hS hM hMS]
  rw [cpow_nOf, ← Finset.prod_coe_sort S]

theorem sqrt_cpow_sq (M : ℕ) (s : ℂ) :
    (((Real.sqrt M : ℝ) : ℂ) ^ s) ^ 2 = ((M : ℕ) : ℂ) ^ s := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rcases eq_or_ne s 0 with rfl | hs
    · simp
    · simp [Real.sqrt_zero, Complex.zero_cpow hs]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hsq : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.mpr hM'
  rw [← Complex.cpow_nat_mul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hsq.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hM'.ne'), ← Complex.ofReal_log hsq.le,
    Real.log_sqrt hM'.le]
  congr 1
  have : ((M : ℕ) : ℂ) = ((M : ℝ) : ℂ) := by norm_cast
  rw [this, ← Complex.ofReal_log hM'.le]
  push_cast
  ring

end Powers

section ConjPoly

theorem isRoot_map_conj_iff (P : ℂ[X]) (z : ℂ) :
    (P.map (starRingEnd ℂ)).IsRoot z ↔ P.IsRoot (starRingEnd ℂ z) := by
  rw [IsRoot.def, IsRoot.def, Polynomial.eval_map]
  conv_lhs => rw [show z = starRingEnd ℂ (starRingEnd ℂ z) from (Complex.conj_conj z).symm,
    Polynomial.eval₂_hom]
  rw [map_eq_zero]

theorem coeff_map_conj (P : ℂ[X]) (k : ℕ) :
    (P.map (starRingEnd ℂ)).coeff k = starRingEnd ℂ (P.coeff k) := Polynomial.coeff_map _ _

theorem natDegree_map_conj (P : ℂ[X]) : (P.map (starRingEnd ℂ)).natDegree = P.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (starRingEnd ℂ).injective _

end ConjPoly

end DeligneSerreCmp

open DeligneSerreCmp in
theorem solution
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (a b : ℕ → ℂ) (ha₁ : a 1 = 1) (hb₁ : b 1 = 1)
    (hamul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hbmul : ∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n)
    (P Q : ℕ → ℂ[X])
    (hP : ∀ p : ℕ, p.Prime → (P p : PowerSeries ℂ) * PowerSeries.mk (fun k => a (p ^ k)) = 1)
    (hQ : ∀ p : ℕ, p.Prime → (Q p : PowerSeries ℂ) * PowerSeries.mk (fun k => b (p ^ k)) = 1)
    (hPQ : ∀ p : ℕ, p.Prime → p ∉ S → P p = Q p)
    (hProots : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1)
    (hQroots : ∀ p ∈ S,
      (∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1))
    (Ma Mb : ℕ) (hMa : Ma ≠ 0) (hMb : Mb ≠ 0)
    (hMS : ∀ p : ℕ, p.Prime → p ∣ Ma * Mb → p ∈ S)
    (G : ℂ → ℂ) (σ₁ : ℝ) (hG : ∀ s : ℝ, σ₁ < s → G s ≠ 0)
    (hsum : ∀ s : ℝ, σ₁ < s → LSeriesSummable a s ∧ LSeriesSummable b s)
    (wa wb : ℂ) (hwa : wa ≠ 0) (hwb : wb ≠ 0)
    (Λa₁ Λa₂ Λa₁' Λa₂' Λb₁ Λb₂ Λb₁' Λb₂' : ℂ → ℂ)
    (hΛa₁ : Differentiable ℂ Λa₁) (hΛa₂ : Differentiable ℂ Λa₂)
    (hΛa₁' : Differentiable ℂ Λa₁') (hΛa₂' : Differentiable ℂ Λa₂')
    (hΛb₁ : Differentiable ℂ Λb₁) (hΛb₂ : Differentiable ℂ Λb₂)
    (hΛb₁' : Differentiable ℂ Λb₁') (hΛb₂' : Differentiable ℂ Λb₂')
    (hΛa : ∀ s : ℝ, σ₁ < s →
      Λa₂ s ≠ 0 ∧ Λa₂' s ≠ 0 ∧
      Λa₁ s = Λa₂ s * (((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries a s) ∧
      Λa₁' s = Λa₂' s *
        (((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries (fun m => starRingEnd ℂ (a m)) s))
    (hΛb : ∀ s : ℝ, σ₁ < s →
      Λb₂ s ≠ 0 ∧ Λb₂' s ≠ 0 ∧
      Λb₁ s = Λb₂ s * (((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries b s) ∧
      Λb₁' s = Λb₂' s *
        (((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries (fun m => starRingEnd ℂ (b m)) s))
    (hFEa₁ : ∀ s : ℂ, Λa₁ (1 - s) = wa * Λa₁' s) (hFEa₂ : ∀ s : ℂ, Λa₂ (1 - s) = Λa₂' s)
    (hFEb₁ : ∀ s : ℂ, Λb₁ (1 - s) = wb * Λb₁' s) (hFEb₂ : ∀ s : ℂ, Λb₂ (1 - s) = Λb₂' s) :
    Ma = Mb ∧ ∀ p ∈ S, P p = Q p := by
  classical

  have hP0 : ∀ p : ℕ, p.Prime → (P p).coeff 0 = 1 := fun p hp =>
    coeff_zero_eq_one_of_mul_mk_eq_one ha₁ (hP p hp)
  have hQ0 : ∀ p : ℕ, p.Prime → (Q p).coeff 0 = 1 := fun p hp =>
    coeff_zero_eq_one_of_mul_mk_eq_one hb₁ (hQ p hp)

  have hconv : a ⍟ corr S P = b ⍟ corr S Q := convolution_corr_eq hS ha₁ hb₁ hamul hbmul hP hQ hPQ
  have hL : ∀ s : ℝ, σ₁ < s →
      LSeries a s * eulerProd S P s = LSeries b s * eulerProd S Q s := by
    intro s hs
    obtain ⟨has, hbs⟩ := hsum s hs
    rw [← LSeries_corr hS P, ← LSeries_corr hS Q,
      ← LSeries_convolution' has (LSeriesSummable_corr hS P _),
      ← LSeries_convolution' hbs (LSeriesSummable_corr hS Q _), hconv]
  set Pc : ℕ → ℂ[X] := fun p => (P p).map (starRingEnd ℂ) with hPc
  set Qc : ℕ → ℂ[X] := fun p => (Q p).map (starRingEnd ℂ) with hQc
  have hLc : ∀ s : ℝ, σ₁ < s →
      LSeries (fun m => starRingEnd ℂ (a m)) s * eulerProd S Pc s =
        LSeries (fun m => starRingEnd ℂ (b m)) s * eulerProd S Qc s := by
    intro s hs
    have h := congrArg (starRingEnd ℂ) (hL s hs)
    rw [map_mul, map_mul, conj_LSeries_ofReal, conj_LSeries_ofReal, conj_eulerProd_ofReal,
      conj_eulerProd_ofReal] at h
    exact h

  have hMa' : (0 : ℝ) < Real.sqrt Ma := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hMa)
  have hMb' : (0 : ℝ) < Real.sqrt Mb := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hMb)
  have hCa0 : ((Real.sqrt Ma : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hMa'.ne'
  have hCb0 : ((Real.sqrt Mb : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hMb'.ne'
  set Ca : ℂ → ℂ := fun s => ((Real.sqrt Ma : ℝ) : ℂ) ^ s with hCa
  set Cb : ℂ → ℂ := fun s => ((Real.sqrt Mb : ℝ) : ℂ) ^ s with hCb
  have hCad : Differentiable ℂ Ca := differentiable_id.const_cpow (Or.inl hCa0)
  have hCbd : Differentiable ℂ Cb := differentiable_id.const_cpow (Or.inl hCb0)
  have hDP := differentiable_eulerProd hS P
  have hDQ := differentiable_eulerProd hS Q
  have hDPc := differentiable_eulerProd hS Pc
  have hDQc := differentiable_eulerProd hS Qc
  set E₁ : ℂ → ℂ := fun s => Λa₁ s * Cb s * eulerProd S P s * Λb₂ s with hE₁
  set E₂ : ℂ → ℂ := fun s => Λb₁ s * Ca s * eulerProd S Q s * Λa₂ s with hE₂
  have hE : E₁ = E₂ := by
    refine eq_of_eq_on_real_gt (((hΛa₁.mul hCbd).mul hDP).mul hΛb₂)
      (((hΛb₁.mul hCad).mul hDQ).mul hΛa₂) σ₁ fun s hs => ?_
    obtain ⟨-, -, ha1, -⟩ := hΛa s hs
    obtain ⟨-, -, hb1, -⟩ := hΛb s hs
    have h := hL s hs
    simp only [hE₁, hE₂, hCa, hCb]
    rw [ha1, hb1]
    calc Λa₂ ↑s * (((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries a s) *
          ((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * eulerProd S P s * Λb₂ s
        = Λa₂ s * Λb₂ s * ((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * ((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) *
            G s * (LSeries a s * eulerProd S P s) := by ring
      _ = Λa₂ s * Λb₂ s * ((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * ((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) *
            G s * (LSeries b s * eulerProd S Q s) := by rw [h]
      _ = Λb₂ ↑s * (((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries b s) *
          ((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * eulerProd S Q s * Λa₂ s := by ring
  set E₁' : ℂ → ℂ := fun s => Λa₁' s * Cb s * eulerProd S Pc s * Λb₂' s with hE₁'
  set E₂' : ℂ → ℂ := fun s => Λb₁' s * Ca s * eulerProd S Qc s * Λa₂' s with hE₂'
  have hE' : E₁' = E₂' := by
    refine eq_of_eq_on_real_gt (((hΛa₁'.mul hCbd).mul hDPc).mul hΛb₂')
      (((hΛb₁'.mul hCad).mul hDQc).mul hΛa₂') σ₁ fun s hs => ?_
    obtain ⟨-, -, -, ha1⟩ := hΛa s hs
    obtain ⟨-, -, -, hb1⟩ := hΛb s hs
    have h := hLc s hs
    simp only [hE₁', hE₂', hCa, hCb]
    rw [ha1, hb1]
    calc Λa₂' ↑s * (((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * G s *
            LSeries (fun m => starRingEnd ℂ (a m)) s) *
          ((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * eulerProd S Pc s * Λb₂' s
        = Λa₂' s * Λb₂' s * ((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * ((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) *
            G s * (LSeries (fun m => starRingEnd ℂ (a m)) s * eulerProd S Pc s) := by ring
      _ = Λa₂' s * Λb₂' s * ((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * ((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) *
            G s * (LSeries (fun m => starRingEnd ℂ (b m)) s * eulerProd S Qc s) := by rw [h]
      _ = Λb₂' ↑s * (((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * G s *
            LSeries (fun m => starRingEnd ℂ (b m)) s) *
          ((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * eulerProd S Qc s * Λa₂' s := by ring

  obtain ⟨σL, hσL⟩ : ∃ σ : ℝ, ∀ s : ℝ, σ < s → LSeries (fun m => starRingEnd ℂ (b m)) s ≠ 0 :=
    exists_LSeries_ne_zero (by simp [hb₁]) (LSeriesSummable_conj (hsum (σ₁ + 1) (by linarith)).2)
  set σ₀ : ℝ := max σ₁ σL + 1 with hσ₀
  set e : ℕ → ℤ := fun p => (Mb.factorization p : ℤ) - (Ma.factorization p : ℤ) with he
  set ω : ℂ := wb * ((Real.sqrt Ma : ℝ) : ℂ) / (wa * ((Real.sqrt Mb : ℝ) : ℂ)) with hω
  have hω0 : ω ≠ 0 := div_ne_zero (mul_ne_zero hwb hCa0) (mul_ne_zero hwa hCb0)
  have hMaS : Ma.primeFactors ⊆ S := fun p hp =>
    hMS p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans (dvd_mul_right _ _))
  have hMbS : Mb.primeFactors ⊆ S := fun p hp =>
    hMS p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans (dvd_mul_left _ _))
  have key : ∀ s : ℝ, σ₀ ≤ s →
      (∏ p ∈ S, ((p : ℂ) ^ (-(s : ℂ))) ^ (e p)) *
          ∏ p ∈ S, (P p).eval ((p : ℂ) ^ ((s : ℂ) - 1)) * (Qc p).eval ((p : ℂ) ^ (-(s : ℂ))) =
        ω * ∏ p ∈ S, (Pc p).eval ((p : ℂ) ^ (-(s : ℂ))) * (Q p).eval ((p : ℂ) ^ ((s : ℂ) - 1)) := by
    intro s hs
    have hs₁ : σ₁ < s := by
      have := le_max_left σ₁ σL; linarith
    have hsL : σL < s := by
      have := le_max_right σ₁ σL; linarith
    obtain ⟨_, hΛa₂'0, -, -⟩ := hΛa s hs₁
    obtain ⟨_, hΛb₂'0, -, hΛb₁'eq⟩ := hΛb s hs₁
    have hΛb₁'0 : Λb₁' s ≠ 0 := by
      rw [hΛb₁'eq]
      refine mul_ne_zero hΛb₂'0 (mul_ne_zero (mul_ne_zero ?_ (hG s hs₁)) (hσL s hsL))
      exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hCb0))

    have h1 := congrFun hE (1 - (s : ℂ))
    simp only [hE₁, hE₂] at h1
    rw [hFEa₁, hFEa₂, hFEb₁, hFEb₂] at h1

    have h2 := congrFun hE' (s : ℂ)
    simp only [hE₁', hE₂'] at h2

    have h3 : wa * Cb (1 - s) * eulerProd S P (1 - s) * (Λb₁' s * Ca s * eulerProd S Qc s * Λa₂' s) =
        wb * Λb₁' s * Ca (1 - s) * eulerProd S Q (1 - s) * Λa₂' s * (Cb s * eulerProd S Pc s) := by
      rw [← h2]
      linear_combination (Cb ↑s * eulerProd S Pc ↑s) * h1

    have h4 : wa * Cb (1 - s) * Ca s * eulerProd S P (1 - s) * eulerProd S Qc s =
        wb * Ca (1 - s) * Cb s * eulerProd S Q (1 - s) * eulerProd S Pc s := by
      have hne : Λb₁' s * Λa₂' s ≠ 0 := mul_ne_zero hΛb₁'0 hΛa₂'0
      apply mul_left_cancel₀ hne
      linear_combination h3

    have hCa1 : Ca (1 - s) = ((Real.sqrt Ma : ℝ) : ℂ) * (Ca s)⁻¹ := by
      simp only [hCa]
      rw [Complex.cpow_sub _ _ hCa0, Complex.cpow_one, div_eq_mul_inv]
    have hCb1 : Cb (1 - s) = ((Real.sqrt Mb : ℝ) : ℂ) * (Cb s)⁻¹ := by
      simp only [hCb]
      rw [Complex.cpow_sub _ _ hCb0, Complex.cpow_one, div_eq_mul_inv]
    have hCas0 : Ca s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hCa0)
    have hCbs0 : Cb s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hCb0)

    have hx : ∀ p ∈ S, ((p : ℂ) ^ (-(s : ℂ))) ≠ 0 := fun p hp =>
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hS p hp).ne_zero))
    have hprod : (∏ p ∈ S, ((p : ℂ) ^ (-(s : ℂ))) ^ (e p)) = (Ca s) ^ 2 * ((Cb s) ^ 2)⁻¹ := by
      have hMa1 : ((Ma : ℕ) : ℂ) ^ (-(s : ℂ)) = ∏ p ∈ S, (((p : ℂ) ^ (-(s : ℂ)))) ^ (Ma.factorization p) :=
        natCast_cpow_eq_prod hS hMa hMaS _
      have hMb1 : ((Mb : ℕ) : ℂ) ^ (-(s : ℂ)) = ∏ p ∈ S, (((p : ℂ) ^ (-(s : ℂ)))) ^ (Mb.factorization p) :=
        natCast_cpow_eq_prod hS hMb hMbS _
      have hzpow : ∀ p ∈ S, ((p : ℂ) ^ (-(s : ℂ))) ^ (e p) =
          (((p : ℂ) ^ (-(s : ℂ)))) ^ (Mb.factorization p) / (((p : ℂ) ^ (-(s : ℂ)))) ^ (Ma.factorization p) := by
        intro p hp
        simp only [he]
        rw [zpow_sub₀ (hx p hp), zpow_natCast, zpow_natCast]
      rw [Finset.prod_congr rfl hzpow, Finset.prod_div_distrib, ← hMa1, ← hMb1,
        sqrt_cpow_sq, sqrt_cpow_sq, Complex.cpow_neg, Complex.cpow_neg]
      field_simp

    rw [hprod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    rw [hCa1, hCb1] at h4
    simp only [eulerProd, neg_sub] at h4 ⊢
    simp only [hω]
    field_simp at h4
    field_simp
    linear_combination h4

  have hPc0 : ∀ p ∈ S, (Pc p).coeff 0 = 1 := fun p hp => by
    simp only [hPc, coeff_map_conj, hP0 p (hS p hp), map_one]
  have hQc0 : ∀ p ∈ S, (Qc p).coeff 0 = 1 := fun p hp => by
    simp only [hQc, coeff_map_conj, hQ0 p (hS p hp), map_one]
  have hProots' : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → 1 < ‖z‖ ^ 2 * p := by
    intro p hp z hz
    rw [hProots p hp z hz, one_pow, one_mul]
    exact_mod_cast (hS p hp).one_lt
  have hPcroots1 : ∀ p ∈ S, ∀ z : ℂ, (Pc p).IsRoot z → ‖z‖ = 1 := by
    intro p hp z hz
    rw [hPc, isRoot_map_conj_iff] at hz
    rw [← RCLike.norm_conj z]
    exact hProots p hp _ hz
  have hPcroots' : ∀ p ∈ S, ∀ z : ℂ, (Pc p).IsRoot z → 1 < ‖z‖ ^ 2 * p := by
    intro p hp z hz
    rw [hPcroots1 p hp z hz, one_pow, one_mul]
    exact_mod_cast (hS p hp).one_lt
  have hQalt : ∀ p ∈ S,
      ((∀ z : ℂ, (Qc p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∧
          ∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((∀ z : ℂ, (Pc p).IsRoot z → ‖z‖ = 1) ∧ (∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1) ∧
          (Qc p).natDegree ≤ 2 ∧ ‖(Qc p).coeff 2‖ = 1 ∧
          (Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1) := by
    intro p hp
    rcases hQroots p hp with h | ⟨hdeg, hc2⟩
    · left
      refine ⟨fun z hz => ?_, h⟩
      rw [hQc, isRoot_map_conj_iff] at hz
      rw [← RCLike.norm_conj z]
      exact h _ hz
    · right
      refine ⟨hPcroots1 p hp, hProots p hp, ?_, ?_, hdeg, hc2⟩
      · rw [hQc]; simp only [natDegree_map_conj]; exact hdeg
      · rw [hQc]; simp only [coeff_map_conj, RCLike.norm_conj]; exact hc2

  have hL49 := DeligneSerre.eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
    S hS e ω hω0 Pc Qc P Q hPc0 hQc0 (fun p hp => hP0 p (hS p hp)) (fun p hp => hQ0 p (hS p hp))
    hPcroots' hProots' hQalt σ₀ key
  refine ⟨?_, fun p hp => (hL49 p hp).2.2⟩
  refine Nat.eq_of_factorization_eq hMa hMb fun p => ?_
  by_cases hpS : p ∈ S
  · have h0 := (hL49 p hpS).1
    simp only [he] at h0
    omega
  · by_cases hp : p.Prime
    · have hndvd : ¬ p ∣ Ma * Mb := fun h => hpS (hMS p hp h)
      rw [Nat.factorization_eq_zero_of_not_dvd fun h => hndvd (h.trans (dvd_mul_right _ _)),
        Nat.factorization_eq_zero_of_not_dvd fun h => hndvd (h.trans (dvd_mul_left _ _))]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

end

end S_DeligneSerre_eq_of_eulerProduct_completedLSeries_functionalEquation
end P2MW
export P2MW.S_DeligneSerre_eq_of_eulerProduct_completedLSeries_functionalEquation (solution)
