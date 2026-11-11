-- Prove2me | solution 1 for GamblersFallacy.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T10:27:31.021573+00:00
-- url     : https://prove2.me/submissions/0b5a50d7-1136-4772-93ff-068c650474bb

import Definitions.Def_GamblersFallacy_biasedEstimate
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.Monotone.Basic

-- Component: P026Data
set_option autoImplicit false

open scoped BigOperators
open GamblersFallacy

namespace S02Gambler

noncomputable section

def bit (b : Bool) : ℝ := if b then 1 else 0

def count {n : ℕ} (ω : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun k => ω k = true)).card

def startNum {m : ℕ} (ν : Fin (m + 1) → Bool) : ℝ :=
  bit (ν 0) + ∑ j : Fin m, bit (ν j.castSucc) * bit (ν j.succ)

def prefixGen (m : ℕ) (p t : ℝ) : ℝ :=
  ∑ ν : Fin (m + 1) → Bool,
    pathWeight p ν * t ^ count ν * (startNum ν + p * bit (ν (Fin.last m)))

end

end S02Gambler

-- Component: P026Generating
set_option autoImplicit false
open scoped BigOperators
open GamblersFallacy

namespace S02Gambler
noncomputable section

lemma pow_count_eq_prod {n : ℕ} (t : ℝ) (ν : Fin n → Bool) :
    t ^ count ν = ∏ j, if ν j then t else 1 := by
  classical
  rw [count, ← Finset.prod_const]
  exact Finset.prod_filter _ _

lemma pathWeight_mul_pow_count {n : ℕ} (p t : ℝ) (ν : Fin n → Bool) :
    pathWeight p ν * t ^ count ν = ∏ j, if ν j then p * t else 1 - p := by
  classical
  rw [pathWeight, pow_count_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  cases ν j <;> simp

lemma marked_product_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (a b : ℝ) :
    (∑ ν : ι → Bool, (∏ j, if ν j then a else b) * ∏ j ∈ A, bit (ν j)) =
      a ^ A.card * (b + a) ^ (Fintype.card ι - A.card) := by
  classical
  calc
    _ = ∑ ν : ι → Bool,
        ∏ j, ((if ν j then a else b) * if j ∈ A then bit (ν j) else 1) := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
    _ = ∏ j, ∑ z : Bool, ((if z then a else b) * if j ∈ A then bit z else 1) :=
      (Fintype.prod_sum (fun (j : ι) (z : Bool) =>
        (if z then a else b) * if j ∈ A then bit z else 1)).symm
    _ = ∏ j : ι, if j ∈ A then a else b + a := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j ∈ A <;> simp [Fintype.univ_bool, bit, hj, add_comm]
    _ = _ := by
      rw [Finset.prod_ite]
      have hA : Finset.univ.filter (fun j : ι => j ∈ A) = A := by ext j; simp
      have hAc : Finset.univ.filter (fun j : ι => j ∉ A) = Aᶜ := by ext j; simp
      rw [hA, hAc]
      simp [Finset.card_compl]

lemma tilted_marked_sum {n : ℕ} (A : Finset (Fin n)) (p t : ℝ) :
    (∑ ν : Fin n → Bool,
      pathWeight p ν * t ^ count ν * ∏ j ∈ A, bit (ν j)) =
      (p * t) ^ A.card * (1 - p + p * t) ^ (n - A.card) := by
  simp_rw [pathWeight_mul_pow_count]
  simpa using marked_product_sum A (p * t) (1 - p)

lemma tilted_singleton_sum {n : ℕ} (j : Fin (n + 1)) (p t : ℝ) :
    (∑ ν : Fin (n + 1) → Bool,
      pathWeight p ν * t ^ count ν * bit (ν j)) =
      p * t * (1 - p + p * t) ^ n := by
  simpa using tilted_marked_sum {j} p t

lemma tilted_pair_sum {n : ℕ} (a b : Fin n) (hab : a ≠ b) (p t : ℝ) :
    (∑ ν : Fin n → Bool,
      pathWeight p ν * t ^ count ν * (bit (ν a) * bit (ν b))) =
      p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (n - 2) := by
  simpa [hab, mul_pow] using tilted_marked_sum {a, b} p t

lemma prefixGen_eq (m : ℕ) (p t : ℝ) :
    prefixGen m p t =
      p * (1 + p) * t * (1 - p + p * t) ^ m +
      (m : ℝ) * p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1) := by
  classical
  have hlast :
      (∑ ν : Fin (m + 1) → Bool,
        pathWeight p ν * t ^ count ν * (p * bit (ν (Fin.last m)))) =
        p * (p * t * (1 - p + p * t) ^ m) := by
    calc
      _ = p * ∑ ν : Fin (m + 1) → Bool,
          pathWeight p ν * t ^ count ν * bit (ν (Fin.last m)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ν _
        ring
      _ = _ := by rw [tilted_singleton_sum]
  have hpairs :
      (∑ j : Fin m, ∑ ν : Fin (m + 1) → Bool,
        pathWeight p ν * t ^ count ν * (bit (ν j.castSucc) * bit (ν j.succ))) =
        (m : ℝ) * p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1) := by
    calc
      _ = ∑ j : Fin m, p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : j.castSucc ≠ j.succ := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castSucc, Fin.val_succ] at hv
          omega
        rw [tilted_pair_sum _ _ hj]
        have hpow : m + 1 - 2 = m - 1 := by omega
        rw [hpow]
      _ = _ := by simp; ring
  have hexpand : prefixGen m p t =
      (∑ ν : Fin (m + 1) → Bool, pathWeight p ν * t ^ count ν * bit (ν 0)) +
      (∑ j : Fin m, ∑ ν : Fin (m + 1) → Bool,
        pathWeight p ν * t ^ count ν * (bit (ν j.castSucc) * bit (ν j.succ))) +
      (∑ ν : Fin (m + 1) → Bool,
        pathWeight p ν * t ^ count ν * (p * bit (ν (Fin.last m)))) := by
    simp only [prefixGen, startNum, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  rw [hexpand, tilted_singleton_sum, hpairs, hlast]
  ring


end
end S02Gambler

-- Component: P026Empirical
set_option autoImplicit false

open scoped BigOperators
open GamblersFallacy

namespace S02Gambler

@[simp] theorem bit_true : bit true = 1 := rfl
@[simp] theorem bit_false : bit false = 0 := rfl

theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by
  cases a <;> cases b <;> norm_num [bit]

/-- A cardinality of true bits is the sum of their real indicators. -/
theorem sum_bit_eq_count {n : ℕ} (ω : Fin n → Bool) :
    (∑ k, bit (ω k)) = (count ω : ℝ) := by
  simp only [count, Finset.natCast_card_filter, bit]

@[simp] theorem arrival_zero {n : ℕ} (ω : Fin n → Bool) : arrival ω 0 = true := by
  simp [arrival]

theorem arrival_succ {n : ℕ} (ω : Fin n → Bool) (k : Fin n) :
    arrival ω (k.val + 1) = ω k := by
  have hk : k.val + 1 ≤ n := by omega
  simp [arrival, hk]

@[simp] theorem arrival_snoc_succ {n : ℕ} (ν : Fin n → Bool) (b : Bool)
    (k : Fin n) : arrival (Fin.snoc ν b) (k.val + 1) = ν k := by
  simpa only [Fin.val_castSucc, Fin.snoc_castSucc] using
    arrival_succ (Fin.snoc ν b) k.castSucc

/-- For a unit gap, the open interval between its endpoints is empty. -/
theorem gap_one {n : ℕ} (ω : Fin n → Bool) (k : Fin n) :
    gapAt ω 1 k.val = (arrival ω k.val && ω k) := by
  have hk : k.val + 1 ≤ n := by omega
  have hempty : Finset.Ioo k.val (k.val + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have hbounds := Finset.mem_Ioo.mp hl
    omega
  simp [gapAt, hk, hempty, arrival_succ]

/-- The denominator counts the fixed arrival and all true prefix bits. -/
theorem denominator_snoc (m : ℕ) (ν : Fin (m + 1) → Bool) (b : Bool) :
    ((((Finset.range (m + 2)).filter
      (fun t => arrival (Fin.snoc ν b) t = true)).card : ℝ)) =
        (count ν : ℝ) + 1 := by
  rw [Finset.natCast_card_filter]
  change (∑ t ∈ Finset.range (m + 2), bit (arrival (Fin.snoc ν b) t)) = _
  rw [Finset.sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, arrival_zero, bit_true, Fin.val_succ, arrival_snoc_succ,
    sum_bit_eq_count]
  exact add_comm _ _

/-- The numerator consists of the first arrival, internal adjacent pairs, and
the pair closing at the final random position. -/
theorem numerator_snoc (m : ℕ) (ν : Fin (m + 1) → Bool) (b : Bool) :
    ((((Finset.range (m + 2)).filter
      (fun t => gapAt (Fin.snoc ν b) 1 t = true)).card : ℝ)) =
        startNum ν + bit (ν (Fin.last m)) * bit b := by
  rw [Finset.natCast_card_filter]
  change (∑ t ∈ Finset.range (m + 2), bit (gapAt (Fin.snoc ν b) 1 t)) = _
  rw [Finset.sum_range]
  simp_rw [gap_one, bit_and]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, arrival_zero, bit_true, one_mul, Fin.val_succ,
    arrival_snoc_succ]
  have hzero : (Fin.snoc ν b : Fin (m + 2) → Bool) 0 = ν 0 := by
    simp only [Fin.snoc_apply_zero]
  rw [hzero, Fin.sum_univ_castSucc]
  simp only [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  exact (add_assoc _ _ _).symm

/-- The original empirical statistic in exact prefix/last-bit form. -/
theorem empirical_snoc (m : ℕ) (ν : Fin (m + 1) → Bool) (b : Bool) :
    empiricalGap (m + 2) 1 (Fin.snoc ν b) =
      (startNum ν + bit (ν (Fin.last m)) * bit b) / ((count ν : ℝ) + 1) := by
  simp only [empiricalGap, numerator_snoc, denominator_snoc]

/-- The last independent bit factors out of the published path weight. -/
theorem pathWeight_snoc {n : ℕ} (p : ℝ) (ν : Fin n → Bool) (b : Bool) :
    pathWeight p (Fin.snoc ν b) = pathWeight p ν * (if b then p else 1 - p) := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Average the last independent bit in the exact published path expectation. -/
theorem biased_prefix (m : ℕ) (p : ℝ) :
    biasedEstimate (m + 2) 1 p =
      ∑ ν : Fin (m + 1) → Bool,
        pathWeight p ν * (startNum ν + p * bit (ν (Fin.last m))) /
          ((count ν : ℝ) + 1) := by
  classical
  unfold biasedEstimate
  let e := Fin.snocEquiv (fun _ : Fin (m + 2) => Bool)
  rw [← e.sum_comp (fun ω => pathWeight p ω * empiricalGap (m + 2) 1 ω)]
  rw [Fintype.sum_prod_type]
  change (∑ b : Bool, ∑ ν : Fin (m + 1) → Bool,
    pathWeight p (Fin.snoc ν b) * empiricalGap (m + 2) 1 (Fin.snoc ν b)) = _
  rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ν _
  simp only [pathWeight_snoc, empirical_snoc]
  cases hlast : ν (Fin.last m) <;> simp [bit, hlast] <;> ring

end S02Gambler

-- Component: P026Integral
set_option autoImplicit false

open scoped BigOperators
open GamblersFallacy MeasureTheory

namespace S02Gambler

/-- Integrating a path's generating monomial supplies its reciprocal arrival
count. This identity is valid for every real parameter. -/
theorem integral_prefixGen_eq_sum (m : ℕ) (p : ℝ) :
    (∫ t in (0 : ℝ)..1, prefixGen m p t) =
      ∑ ν : Fin (m + 1) → Bool,
        pathWeight p ν * (startNum ν + p * bit (ν (Fin.last m))) /
          ((count ν : ℝ) + 1) := by
  have hcont (ν : Fin (m + 1) → Bool) : Continuous (fun t : ℝ =>
      pathWeight p ν * t ^ count ν * (startNum ν + p * bit (ν (Fin.last m)))) := by
    fun_prop
  unfold prefixGen
  rw [intervalIntegral.integral_finsetSum
    (fun ν _ => (hcont ν).intervalIntegrable 0 1)]
  apply Finset.sum_congr rfl
  intro ν _
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  ring

/-- Differentiation of the polynomial primitive. The natural-power derivative
formula also handles `m = 0`, because its second term has coefficient zero. -/
theorem primitive_hasDerivAt (m : ℕ) (p t : ℝ) :
    HasDerivAt (fun x : ℝ => p * x ^ 2 * (1 - p + p * x) ^ m)
      (p * (1 + p) * t * (1 - p + p * t) ^ m +
        (m : ℝ) * p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1) +
        p * (1 - p) * (t * (1 - p + p * t) ^ m)) t := by
  have ht : HasDerivAt (fun x : ℝ => p * x ^ 2) (p * (2 * t)) t := by
    simpa using (((hasDerivAt_id t).fun_pow 2).const_mul p)
  have hq : HasDerivAt (fun x : ℝ => 1 - p + p * x) p t := by
    simpa using ((hasDerivAt_id t).const_mul p).const_add (1 - p)
  convert ht.fun_mul (hq.fun_pow m) using 1 <;> first | rfl | ring

/-- The closed generating polynomial integrates to the expectation formula. -/
theorem integral_generating_formula (m : ℕ) (p : ℝ) :
    (∫ t in (0 : ℝ)..1,
      p * (1 + p) * t * (1 - p + p * t) ^ m +
        (m : ℝ) * p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1)) =
      p - p * (1 - p) * (∫ t in (0 : ℝ)..1, t * (1 - p + p * t) ^ m) := by
  have hF : Continuous (fun t : ℝ =>
      p * (1 + p) * t * (1 - p + p * t) ^ m +
        (m : ℝ) * p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1)) := by
    fun_prop
  have hC : Continuous (fun t : ℝ =>
      p * (1 - p) * (t * (1 - p + p * t) ^ m)) := by
    fun_prop
  have htotal : (∫ t in (0 : ℝ)..1,
      (p * (1 + p) * t * (1 - p + p * t) ^ m +
        (m : ℝ) * p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1)) +
          p * (1 - p) * (t * (1 - p + p * t) ^ m)) = p := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => primitive_hasDerivAt m p t)
      ((hF.add hC).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add (hF.intervalIntegrable 0 1)
    (hC.intervalIntegrable 0 1), intervalIntegral.integral_const_mul] at htotal
  linarith

/-- Combine the exact finite-path expectation bridge with the independently
proved generating-polynomial identity. Both identities remain explicit inputs
so this file can compile before their separate proof modules finish. -/
theorem biased_integral_of_identities (m : ℕ) (p : ℝ)
    (hprefix : biasedEstimate (m + 2) 1 p =
      ∑ ν : Fin (m + 1) → Bool,
        pathWeight p ν * (startNum ν + p * bit (ν (Fin.last m))) /
          ((count ν : ℝ) + 1))
    (hgen : ∀ t : ℝ, prefixGen m p t =
      p * (1 + p) * t * (1 - p + p * t) ^ m +
        (m : ℝ) * p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1)) :
    biasedEstimate (m + 2) 1 p =
      p - p * (1 - p) * (∫ t in (0 : ℝ)..1, t * (1 - p + p * t) ^ m) := by
  rw [hprefix, ← integral_prefixGen_eq_sum m p]
  simp_rw [hgen]
  exact integral_generating_formula m p

theorem relative_bias_integral_of_identities (m : ℕ) (p : ℝ) (hp : p ≠ 0)
    (hprefix : biasedEstimate (m + 2) 1 p =
      ∑ ν : Fin (m + 1) → Bool,
        pathWeight p ν * (startNum ν + p * bit (ν (Fin.last m))) /
          ((count ν : ℝ) + 1))
    (hgen : ∀ t : ℝ, prefixGen m p t =
      p * (1 + p) * t * (1 - p + p * t) ^ m +
        (m : ℝ) * p ^ 2 * t ^ 2 * (1 - p + p * t) ^ (m - 1)) :
    (p - biasedEstimate (m + 2) 1 p) / p =
      (1 - p) * (∫ t in (0 : ℝ)..1, t * (1 - p + p * t) ^ m) := by
  rw [biased_integral_of_identities m p hprefix hgen]
  field_simp
  ring

end S02Gambler

-- Component: P026Bridge
set_option autoImplicit false

open GamblersFallacy MeasureTheory

namespace S02Gambler

/-- The bias representation derived from the original finite Boolean-path
expectation, with no assumption of an external closed-form formula. -/
theorem relative_bias_integral (m : ℕ) (p : ℝ) (hp : p ≠ 0) :
    (p - biasedEstimate (m + 2) 1 p) / p =
      (1 - p) * (∫ t in (0 : ℝ)..1, t * (1 - p + p * t) ^ m) :=
  relative_bias_integral_of_identities m p hp (biased_prefix m p) (prefixGen_eq m p)

end S02Gambler

-- Component: P026Parameter
set_option autoImplicit false
open MeasureTheory

namespace S02Gambler

/-- Parameter monotonicity of the exact integral bias representation.
The endpoint t = 1 supplies strictness for every horizon, including m = 0. -/
theorem biasIntegral_strictAntiOn_p (m : ℕ) :
    StrictAntiOn (fun p : ℝ =>
      (1 - p) * (∫ t in (0 : ℝ)..1, t * (1 - p + p * t) ^ m)) (Set.Ioo 0 1) := by
  intro p hp q hq hpq
  dsimp only
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1)
  · fun_prop
  · fun_prop
  · intro t ht
    have hbaseq : 0 ≤ 1 - q + q * t := by
      have hqt := mul_nonneg hq.1.le ht.1.le
      linarith [hq.2]
    have hbase : 1 - q + q * t ≤ 1 - p + p * t := by
      have hd := mul_nonneg (sub_nonneg.mpr hpq.le) (sub_nonneg.mpr ht.2)
      nlinarith
    have hpow := pow_le_pow_left₀ hbaseq hbase m
    apply mul_le_mul (by linarith : 1 - q ≤ 1 - p)
      (mul_le_mul_of_nonneg_left hpow ht.1.le)
      (mul_nonneg ht.1.le (pow_nonneg hbaseq m))
    linarith [hp.2]
  · refine ⟨1, by simp, ?_⟩
    simpa using (sub_lt_sub_left hpq 1)

end S02Gambler

-- Component: P026Horizon
set_option autoImplicit false

namespace S02Gambler

/-- Increasing the horizon exponent strictly decreases the bias integral.
The integrands are ordered everywhere and differ strictly at the midpoint. -/
theorem biasIntegral_succ_lt (m : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - p) * (∫ t in (0 : ℝ)..1, t * (1 - p + p * t) ^ (m + 1)) <
      (1 - p) * (∫ t in (0 : ℝ)..1, t * (1 - p + p * t) ^ m) := by
  apply mul_lt_mul_of_pos_left _ (sub_pos.mpr hp.2)
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num) (by fun_prop) (by fun_prop)
  · intro t ht
    have hb0 : 0 ≤ 1 - p + p * t :=
      add_nonneg (sub_nonneg.mpr hp.2.le) (mul_nonneg hp.1.le ht.1.le)
    have hb1 : 1 - p + p * t ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2 hp.1.le
      linarith
    have hpow : (1 - p + p * t) ^ (m + 1) ≤ (1 - p + p * t) ^ m := by
      rw [pow_succ]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hb1 (pow_nonneg hb0 m)
    exact mul_le_mul_of_nonneg_left hpow ht.1.le
  · refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    have hb0 : 0 < 1 - p + p * (1 / 2 : ℝ) := by linarith [hp.2]
    have hb1 : 1 - p + p * (1 / 2 : ℝ) < 1 := by linarith [hp.1]
    have hpow : (1 - p + p * (1 / 2 : ℝ)) ^ (m + 1) <
        (1 - p + p * (1 / 2 : ℝ)) ^ m := by
      rw [pow_succ]
      simpa only [mul_one] using
        mul_lt_mul_of_pos_left hb1 (pow_pos hb0 m)
    exact mul_lt_mul_of_pos_left hpow (by norm_num)

theorem biasIntegral_strictAnti_m (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    StrictAnti (fun m : ℕ =>
      (1 - p) * (∫ t in (0 : ℝ)..1, t * (1 - p + p * t) ^ m)) := by
  exact strictAnti_nat_of_succ_lt (fun m => biasIntegral_succ_lt m p hp)

end S02Gambler

-- Component: P026
set_option autoImplicit false

open GamblersFallacy S02Gambler

/-- The unchanged full root, with both strictness conclusions on their original domains. -/
theorem solution :
    (∀ n : ℕ, 2 ≤ n →
      StrictAntiOn (fun p : ℝ => (p - biasedEstimate n 1 p) / p) (Set.Ioo 0 1)) ∧
    (∀ p ∈ Set.Ioo (0 : ℝ) 1,
      StrictAntiOn (fun n : ℕ => (p - biasedEstimate n 1 p) / p) {n : ℕ | 2 ≤ n}) := by
  constructor
  · intro n hn p hp q hq hpq
    dsimp only
    have hn' : n = (n - 2) + 2 := by omega
    rw [hn', relative_bias_integral _ q (ne_of_gt hq.1),
      relative_bias_integral _ p (ne_of_gt hp.1)]
    exact biasIntegral_strictAntiOn_p (n - 2) hp hq hpq
  · intro p hp a ha b hb hab
    dsimp only
    change 2 ≤ a at ha
    change 2 ≤ b at hb
    have ha' : a = (a - 2) + 2 := by omega
    have hb' : b = (b - 2) + 2 := by omega
    rw [ha', hb', relative_bias_integral _ p (ne_of_gt hp.1),
      relative_bias_integral _ p (ne_of_gt hp.1)]
    exact biasIntegral_strictAnti_m p hp (by omega)

#print axioms solution
