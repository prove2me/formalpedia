-- Prove2me | solution 1 for BroughanRH.landauPrincipalValue
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T20:06:51.782824+00:00
-- url     : https://prove2.me/submissions/02a2ba3b-0b66-4083-8b8c-5148ffef7caa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LandauFunction_landau
import Definitions.Def_LandauFunction_logIntegral
import Theorems.Thm_LandauCriterion_psi1_error_of_riemannHypothesis
import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis
import Theorems.Thm_riemann_hypothesis

/-!
# RH ⇒ `log g(n) < √(Li⁻¹ n)` for all large `n`

`log g(n) ≤ λ n + M(x)` (`LandauRH.log_landau_le`), `x = √(Li⁻¹ n)`; the main inequality
`x - λ Li(x²) - M(x) > 0` follows from the `ψ₁` bound (`LandauCriterion.psi1_error_of_riemannHypothesis`)
and von Koch's bound (`LandauCriterion.psi_error_of_riemannHypothesis`) by partial summation.
-/

namespace LandauMellin end LandauMellin
namespace ZetaAux end ZetaAux
namespace PsiOscillation end PsiOscillation
namespace VonKoch end VonKoch
namespace LandauRH end LandauRH

noncomputable section

-- ===== VK2Perron.lean =====
section

open Complex MeasureTheory Filter Topology Set

namespace VonKoch

open ArithmeticFunction

/-- The Riesz mean `ψ₁(x) = ∑_n Λ(n) (x - n)₊`. -/
def psi1 (x : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * max (x - n) 0

/-! ### Elementary bounds -/

/-! ### The Mellin transform of `(1 - u)₊` -/

/-! ### The Perron formula for `ψ₁` -/

end VonKoch

end

-- ===== VK4Zeta.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric

namespace VonKoch

open ZetaAux ArithmeticFunction

/-! ### Upper and lower bounds for `h(s) = (s-1)ζ(s)` -/

/-! ### Consequences of the Riemann hypothesis for the zeros of `h` -/

lemma one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact (Real.exp_one_lt_d9.trans (by norm_num)).le

lemma one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x :=
  one_le_log_three.trans (Real.log_le_log (by norm_num) hx)

end VonKoch

end

-- ===== VK6Final.lean =====
section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Interval

namespace VonKoch

open ZetaAux ArithmeticFunction

/-! ### The difference kernel `D(s) = ((X+H)^{s+1} - X^{s+1}) / (s(s+1))` -/

/-! ### Continuity of `F` -/

/-! ### Perron's formula for the difference kernel -/

/-! ### Differencing `ψ₁` -/

lemma psi1_eq_sum_range {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : x < N) :
    psi1 x = ∑ n ∈ Finset.range N, Λ n * max (x - n) 0 := by
  rw [psi1]
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_range] at hn ⊢
    have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
    have h2 : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp hn
    have : (n : ℝ) < N := by linarith
    exact_mod_cast this
  · intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    have : x < n := by
      have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
      have h2 := Nat.lt_floor_add_one x
      linarith
    rw [max_eq_right (by linarith), mul_zero]

/-! ### Bounds for the pieces of the contour -/

end VonKoch

end

-- ===== LF4Xi.lean =====
section

set_option autoImplicit false

open Complex MeasureTheory Filter Topology Set Metric
open scoped Interval

namespace LandauRH

open ZetaAux VonKoch

/-! ### Riemann's `ξ` function -/

/-! ### `Γℝ'/Γℝ` and the logarithmic derivative of `ξ` on `Re s > 0` -/

/-! ### The value `2 ξ'/ξ(1) = 2 + γ - log 4π` -/

/-- `S★ = 2 + γ - log 4π`, the sum over zeros of `1/(ρ(1-ρ))`. -/
def Sstar : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

lemma Sstar_lt : Sstar < (2 - Real.sqrt 2) / 3 - 1 / 200 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hlog2 := Real.log_two_gt_d9
  have he := Real.exp_one_lt_d9
  have hlog3 : 2 - Real.exp 1 / 3 ≤ Real.log 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < Real.exp 1 / 3 by positivity)
    rw [Real.log_div (Real.exp_pos 1).ne' (by norm_num), Real.log_exp] at this
    linarith
  have hlog12 : Real.log 12 ≤ Real.log (4 * Real.pi) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have h12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12:ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have hsqrt : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold Sstar
  linarith

/-! ### Multiplicities and symmetry of the zeros -/

/-! ### Bounds for `ξ'/ξ` -/

end LandauRH

end

-- ===== LF7Comb.lean =====
section

set_option autoImplicit false

open Finset

namespace LandauRH

/-! ### The additive function `ℓ(m) = ∑_{p^a ‖ m} p^a` -/

/-- `ℓ(m) = ∑_{p^a ‖ m} p^a`. -/
def ellF (m : ℕ) : ℕ := ∑ p ∈ m.primeFactors, p ^ m.factorization p

lemma sum_le_prod_of_two_le {s : Finset ℕ} {f : ℕ → ℕ} (h : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ha2 := h a (mem_insert_self a s)
    have ih' := ih (fun i hi => h i (mem_insert_of_mem hi))
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs; simp
    · have hP : 2 ≤ ∏ i ∈ s, f i := by
        obtain ⟨b, hb⟩ := hs
        calc 2 ≤ f b := h b (mem_insert_of_mem hb)
          _ ≤ ∏ i ∈ s, f i := by
              apply Nat.le_of_dvd
              · exact Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun i hi => by
                  have := h i (mem_insert_of_mem hi); omega)
              · exact dvd_prod_of_mem f hb
      nlinarith

lemma ellF_le {m : ℕ} (hm : m ≠ 0) : ellF m ≤ m := by
  unfold ellF
  calc ∑ p ∈ m.primeFactors, p ^ m.factorization p
      ≤ ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
        refine sum_le_prod_of_two_le (fun p hp => ?_)
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hv : 1 ≤ m.factorization p := by
          rw [← Nat.support_factorization] at hp
          exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
        calc 2 ≤ p := hpp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ m.factorization p := Nat.pow_le_pow_right hpp.pos hv
    _ = m := Nat.prod_factorization_pow_eq_self hm

lemma ellF_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : ellF (Nat.lcm a b) ≤ ellF a + ellF b := by
  classical
  unfold ellF
  have hpf : (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
    rw [← Nat.support_factorization, ← Nat.support_factorization, ← Nat.support_factorization,
      Nat.factorization_lcm ha hb, Finsupp.support_sup]
  have hfac : ∀ p, (Nat.lcm a b).factorization p = max (a.factorization p) (b.factorization p) := by
    intro p
    rw [Nat.factorization_lcm ha hb]
    rfl
  rw [hpf]
  have hpt : ∀ p ∈ a.primeFactors ∪ b.primeFactors,
      p ^ (Nat.lcm a b).factorization p ≤
        (if p ∈ a.primeFactors then p ^ a.factorization p else 0) +
        (if p ∈ b.primeFactors then p ^ b.factorization p else 0) := by
    intro p hp
    rw [hfac p]
    by_cases hpa : p ∈ a.primeFactors <;> by_cases hpb : p ∈ b.primeFactors
    · rw [if_pos hpa, if_pos hpb]
      rcases le_total (a.factorization p) (b.factorization p) with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    · rw [if_pos hpa, if_neg hpb]
      have : b.factorization p = 0 := by
        rw [← Nat.support_factorization] at hpb
        exact Finsupp.notMem_support_iff.mp hpb
      rw [this, max_eq_left (Nat.zero_le _)]; omega
    · rw [if_neg hpa, if_pos hpb]
      have : a.factorization p = 0 := by
        rw [← Nat.support_factorization] at hpa
        exact Finsupp.notMem_support_iff.mp hpa
      rw [this, max_eq_right (Nat.zero_le _)]; omega
    · exfalso; rcases mem_union.mp hp with h | h <;> contradiction
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, sum_ite_mem, sum_ite_mem, union_inter_cancel_left, union_inter_cancel_right]

lemma ellF_one : ellF 1 = 0 := by simp [ellF]

lemma ellF_multiset_lcm (C : Multiset ℕ) (hC : ∀ c ∈ C, c ≠ 0) : ellF C.lcm ≤ C.sum := by
  induction C using Multiset.induction_on with
  | empty => simp [ellF_one]
  | cons a C ih =>
    rw [Multiset.lcm_cons, Multiset.sum_cons]
    have ha : a ≠ 0 := hC a (Multiset.mem_cons_self a C)
    have hC' : ∀ c ∈ C, c ≠ 0 := fun c hc => hC c (Multiset.mem_cons_of_mem hc)
    have hL : C.lcm ≠ 0 := by
      intro h
      rw [Multiset.lcm_eq_zero_iff] at h
      exact hC' 0 h rfl
    have e : GCDMonoid.lcm a C.lcm = Nat.lcm a C.lcm := rfl
    rw [e]
    calc ellF (Nat.lcm a C.lcm) ≤ ellF a + ellF C.lcm := ellF_lcm ha hL
      _ ≤ a + C.sum := add_le_add (ellF_le ha) (ih hC')

lemma log_eq_sum_factorization {m : ℕ} (hm : m ≠ 0) :
    Real.log m = ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  rw [Finsupp.prod, Nat.cast_prod, Real.log_prod]
  · refine sum_congr rfl (fun p _ => ?_)
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ hpp.ne_zero)

/-! ### The bound `log g(n) ≤ λ n + M(λ)` -/

/-- The increments `p^j - p^{j-1}` (`p^1 - 0` for `j = 1`). -/
def incr (p j : ℕ) : ℝ := (p : ℝ) ^ j - (if j ≤ 1 then 0 else (p : ℝ) ^ (j - 1))

lemma sum_incr (p v : ℕ) : ∑ j ∈ Icc 1 v, incr p j = (p : ℝ) ^ v - (if v = 0 then 1 else 0) := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    unfold incr
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h; simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp

/-- `Δ(p, j) = log p - λ (p^j - p^{j-1})` with `λ = log x / x`. -/
def Delta (x : ℝ) (p j : ℕ) : ℝ := Real.log p - Real.log x / x * incr p j

/-- `M(x) = ∑_{p ≤ x} ∑_{1 ≤ j ≤ A} Δ(p, j)₊`. -/
def Mfun (x : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime,
    ∑ j ∈ Icc 1 (Nat.log 2 ⌊x⌋₊ + 1), max 0 (Delta x p j)

lemma log_div_self_antitone {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    Real.log b / b ≤ Real.log a / a := by
  have := Real.log_div_self_antitoneOn (show a ∈ Set.Ici (Real.exp 1) from ha)
    (show b ∈ Set.Ici (Real.exp 1) from ha.trans hab) hab
  simpa using this

lemma exp_one_le_four : Real.exp 1 ≤ 4 := by
  have := Real.exp_one_lt_d9; linarith

lemma incr_ge (p j : ℕ) (hp : 2 ≤ p) (hj : 1 ≤ j) : (2 : ℝ) ^ (j - 1) ≤ incr p j := by
  unfold incr
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  rcases Nat.lt_or_ge j 2 with h | h
  · have : j = 1 := by omega
    subst this; simp; linarith
  · rw [if_neg (by omega)]
    have e : (p:ℝ) ^ j = p * (p:ℝ) ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]
    have h1 : (2:ℝ) ^ (j - 1) ≤ (p:ℝ) ^ (j - 1) := pow_le_pow_left₀ (by norm_num) hp' _
    have h0 : (0:ℝ) ≤ (p:ℝ) ^ (j - 1) := pow_nonneg (by linarith) _
    nlinarith

/-- Per prime: `v log p - λ p^v ≤ ∑_{j ≤ A} Δ(p, j)₊` for `p ≤ x`. -/
lemma per_prime_le {x : ℝ} (hx : 4 ≤ x) {p v : ℕ} (hp : p.Prime) (hpx : (p:ℝ) ≤ x) (hv : 1 ≤ v) :
    v * Real.log p - Real.log x / x * (p:ℝ) ^ v ≤
      ∑ j ∈ Icc 1 (Nat.log 2 ⌊x⌋₊ + 1), max 0 (Delta x p j) := by
  set A := Nat.log 2 ⌊x⌋₊ + 1 with hA
  have hx0 : 0 < x := by linarith
  have hlam : 0 ≤ Real.log x / x := div_nonneg (Real.log_nonneg (by linarith)) hx0.le
  have hsum : v * Real.log p - Real.log x / x * (p:ℝ) ^ v = ∑ j ∈ Icc 1 v, Delta x p j := by
    unfold Delta
    rw [sum_sub_distrib, sum_const, Nat.card_Icc, ← mul_sum, sum_incr, if_neg (by omega)]
    simp
  rw [hsum]
  have hneg : ∀ j, A < j → Delta x p j < 0 := by
    intro j hj
    unfold Delta
    have h2A : x < (2:ℝ) ^ A := by
      have h1 : ⌊x⌋₊ < 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (2:ℝ) ^ A := by
        rw [hA]; exact_mod_cast h1
      linarith [Nat.lt_floor_add_one x]
    have hinc : (2:ℝ) ^ A ≤ incr p j := by
      refine le_trans ?_ (incr_ge p j hp.two_le (by omega))
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hlogp : Real.log p ≤ Real.log x := Real.log_le_log (by exact_mod_cast hp.pos) hpx
    have : Real.log x < Real.log x / x * incr p j := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hx0]
      have hlx : 0 < Real.log x := Real.log_pos (by linarith)
      nlinarith
    linarith
  calc ∑ j ∈ Icc 1 v, Delta x p j ≤ ∑ j ∈ Icc 1 v, (if j ≤ A then max 0 (Delta x p j) else 0) := by
        refine sum_le_sum (fun j _ => ?_)
        split_ifs with h
        · exact le_max_right _ _
        · exact (hneg j (by omega)).le
    _ = ∑ j ∈ (Icc 1 v).filter (· ≤ A), max 0 (Delta x p j) := by rw [sum_filter]
    _ ≤ ∑ j ∈ Icc 1 A, max 0 (Delta x p j) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [mem_filter, mem_Icc] at hj ⊢
          omega
        · intro j _ _; exact le_max_left _ _

lemma per_prime_large {x : ℝ} (hx : 4 ≤ x) {p v : ℕ} (hp : p.Prime) (hpx : x < (p:ℝ)) (hv : 1 ≤ v) :
    v * Real.log p - Real.log x / x * (p:ℝ) ^ v ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have hlogp : Real.log p / p ≤ Real.log x / x :=
    log_div_self_antitone (exp_one_le_four.trans hx) hpx.le
  have hpow : (v:ℝ) * p ≤ (p:ℝ) ^ v := by
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : ∀ k : ℕ, ((k:ℝ) + 1) * p ≤ (p:ℝ) ^ (k + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ]
        have h3 : ((k:ℝ) + 1 + 1) ≤ (p:ℝ) ^ (k + 1) := by
          have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
        push_cast
        nlinarith
    have := this (v - 1)
    rwa [show v - 1 + 1 = v by omega, show ((v - 1 : ℕ) : ℝ) + 1 = v by
      rw [Nat.cast_sub hv]; ring] at this
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have : (v:ℝ) * Real.log p ≤ Real.log x / x * (v * p) := by
    rw [div_le_div_iff₀ hp0 hx0] at hlogp
    rw [div_mul_eq_mul_div, le_div_iff₀ hx0]
    have hv0 : (0:ℝ) ≤ v := Nat.cast_nonneg v
    nlinarith
  have hlam : 0 ≤ Real.log x / x := div_nonneg (Real.log_nonneg (by linarith)) hx0.le
  nlinarith

lemma Mfun_term_nonneg (x : ℝ) (p : ℕ) :
    0 ≤ ∑ j ∈ Icc 1 (Nat.log 2 ⌊x⌋₊ + 1), max 0 (Delta x p j) :=
  sum_nonneg (fun j _ => le_max_left _ _)

/-- `log L - λ ℓ(L) ≤ M(x)` for every positive integer `L`. -/
lemma log_sub_ellF_le {x : ℝ} (hx : 4 ≤ x) {L : ℕ} (hL : L ≠ 0) :
    Real.log L - Real.log x / x * (ellF L : ℝ) ≤ Mfun x := by
  classical
  rw [log_eq_sum_factorization hL, ellF, Nat.cast_sum, mul_sum, ← sum_sub_distrib]
  calc ∑ p ∈ L.primeFactors, ((L.factorization p : ℝ) * Real.log p -
        Real.log x / x * ((p ^ L.factorization p : ℕ) : ℝ))
      ≤ ∑ p ∈ L.primeFactors, (if (p:ℝ) ≤ x then
          ∑ j ∈ Icc 1 (Nat.log 2 ⌊x⌋₊ + 1), max 0 (Delta x p j) else 0) := by
        refine sum_le_sum (fun p hp => ?_)
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hv : 1 ≤ L.factorization p := by
          rw [← Nat.support_factorization] at hp
          exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
        push_cast
        split_ifs with h
        · exact per_prime_le hx hpp h hv
        · exact per_prime_large hx hpp (not_le.mp h) hv
    _ = ∑ p ∈ L.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ x),
          ∑ j ∈ Icc 1 (Nat.log 2 ⌊x⌋₊ + 1), max 0 (Delta x p j) := by rw [sum_filter]
    _ ≤ Mfun x := by
        unfold Mfun
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [mem_filter, mem_range] at hp ⊢
          refine ⟨?_, Nat.prime_of_mem_primeFactors hp.1⟩
          have := Nat.le_floor hp.2
          omega
        · intro p _ _; exact Mfun_term_nonneg x p

/-- **Upper bound for Landau's function**: `log g(n) ≤ λ n + M(x)` with `λ = log x / x`. -/
theorem log_landau_le (n : ℕ) {x : ℝ} (hx : 4 ≤ x) :
    Real.log (LandauFunction.landau n) ≤ Real.log x / x * n + Mfun x := by
  classical
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Equiv.Perm (Fin n)))
    Finset.univ_nonempty (fun σ => orderOf σ)
  have hland : LandauFunction.landau n = orderOf σ := hσ
  have hL : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  have hlcm : σ.cycleType.lcm = orderOf σ := Equiv.Perm.lcm_cycleType σ
  have hell : ellF (orderOf σ) ≤ n := by
    rw [← hlcm]
    refine (ellF_multiset_lcm _ (fun c hc => by
      have := Equiv.Perm.two_le_of_mem_cycleType hc; omega)).trans ?_
    have := Equiv.Perm.sum_cycleType_le σ
    simpa using this
  rw [hland]
  have h1 := log_sub_ellF_le hx hL
  have hx0 : 0 < x := by linarith
  have hlam : 0 ≤ Real.log x / x := div_nonneg (Real.log_nonneg (by linarith)) hx0.le
  have h2 : Real.log x / x * (ellF (orderOf σ) : ℝ) ≤ Real.log x / x * n :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hell) hlam
  linarith

/-! ### Primorials -/

end LandauRH

end

-- ===== LF7Li.lean =====
section

set_option autoImplicit false

open Set Filter Topology

namespace LandauRH

open LandauFunction

lemma continuousOn_one_div_log : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Ioi 1) := by
  intro t ht
  have ht' : (1:ℝ) < t := ht
  exact (continuousAt_const.div (Real.continuousAt_log (by linarith))
    (Real.log_pos ht').ne').continuousWithinAt

lemma intervalIntegrable_one_div_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_one_div_log.mono (fun t ht => ?_)
  rcases mem_uIcc.mp ht with h | h
  · show 1 < t; linarith [h.1]
  · show 1 < t; linarith [h.1]

lemma hasDerivAt_logIntegral {y : ℝ} (hy : 1 < y) :
    HasDerivAt logIntegral (1 / Real.log y) y := by
  unfold logIntegral
  apply intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_one_div_log
    (by norm_num) hy)
  · exact (continuousOn_one_div_log.stronglyMeasurableAtFilter isOpen_Ioi y hy)
  · exact (continuousOn_one_div_log y hy).continuousAt (isOpen_Ioi.mem_nhds hy)

lemma logIntegral_two : logIntegral 2 = 0 := by simp [logIntegral]

lemma continuousOn_logIntegral : ContinuousOn logIntegral (Ioi 1) := fun y hy =>
  (hasDerivAt_logIntegral hy).continuousAt.continuousWithinAt

lemma logIntegral_le {y : ℝ} (hy : 2 ≤ y) : logIntegral y ≤ (y - 2) / Real.log 2 := by
  unfold logIntegral
  have h := intervalIntegral.integral_mono_on (a := (2:ℝ)) (b := y) (f := fun t => 1 / Real.log t)
    (g := fun _ => 1 / Real.log 2) hy (intervalIntegrable_one_div_log (by norm_num) (by linarith))
    intervalIntegrable_const (fun t ht => by
      apply one_div_le_one_div_of_le (Real.log_pos (by norm_num))
      exact Real.log_le_log (by norm_num) ht.1)
  rw [intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  rw [div_eq_mul_one_div]
  linarith

lemma logIntegral_ge {y : ℝ} (hy : 2 ≤ y) : (y - 2) / Real.log y ≤ logIntegral y := by
  unfold logIntegral
  have h := intervalIntegral.integral_mono_on (a := (2:ℝ)) (b := y) (g := fun t => 1 / Real.log t)
    (f := fun _ => 1 / Real.log y) hy intervalIntegrable_const
    (intervalIntegrable_one_div_log (by norm_num) (by linarith)) (fun t ht => by
      apply one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
      exact Real.log_le_log (by linarith [ht.1]) ht.2)
  rw [intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  rw [div_eq_mul_one_div]
  linarith

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow (Real.sqrt_pos.mpr hx), Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    norm_num
  linarith

/-- `Li(Li⁻¹(n)) = n` and `Li⁻¹(n) ≥ 2` for `n ≥ 0`. -/
theorem logIntegral_logIntegralInv {n : ℝ} (hn : 0 ≤ n) :
    logIntegral (logIntegralInv n) = n ∧ 2 ≤ logIntegralInv n := by
  set S : Set ℝ := {x : ℝ | 2 ≤ x ∧ n ≤ logIntegral x} with hS
  have hbdd : BddBelow S := ⟨2, fun x hx => hx.1⟩
  -- nonempty
  set x₁ : ℝ := (4 * n + 8) ^ 2 with hx₁
  have hx₁64 : 64 ≤ x₁ := by rw [hx₁]; nlinarith
  have hsq : Real.sqrt x₁ = 4 * n + 8 := by rw [hx₁]; exact Real.sqrt_sq (by linarith)
  have hne : S.Nonempty := by
    refine ⟨x₁, by linarith, ?_⟩
    have h1 := logIntegral_ge (y := x₁) (by linarith)
    have h2 := log_le_two_sqrt (x := x₁) (by linarith)
    rw [hsq] at h2
    have hlog : 0 < Real.log x₁ := Real.log_pos (by linarith)
    have h3 : n ≤ (x₁ - 2) / Real.log x₁ := by
      rw [le_div_iff₀ hlog]
      nlinarith
    linarith
  -- closed
  have hclosed : IsClosed S := by
    have hc : ContinuousOn logIntegral (Ici 2) :=
      continuousOn_logIntegral.mono (fun t ht => by show 1 < t; linarith [mem_Ici.mp ht])
    have := hc.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_Ici (a := n))
    convert this using 1
    ext x; simp [hS, and_comm]
  have hmem : sInf S ∈ S := hclosed.csInf_mem hne hbdd
  refine ⟨?_, hmem.1⟩
  have hge : n ≤ logIntegral (sInf S) := hmem.2
  by_contra hne'
  have hgt : n < logIntegral (sInf S) := lt_of_le_of_ne hge (Ne.symm hne')
  have h2 : 2 < sInf S := by
    rcases eq_or_lt_of_le hmem.1 with h | h
    · rw [← h, logIntegral_two] at hgt; linarith
    · exact h
  -- by continuity there is a smaller point of `S`
  have hcont : ContinuousAt logIntegral (sInf S) :=
    (hasDerivAt_logIntegral (by linarith)).continuousAt
  have hev : ∀ᶠ z in 𝓝 (sInf S), n < logIntegral z := hcont.eventually (lt_mem_nhds hgt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set z := sInf S - min (ε / 2) ((sInf S - 2) / 2) with hz
  have hzlt : z < sInf S := by
    have : 0 < min (ε / 2) ((sInf S - 2) / 2) := lt_min (by linarith) (by linarith)
    linarith
  have hz2 : 2 ≤ z := by
    have : min (ε / 2) ((sInf S - 2) / 2) ≤ (sInf S - 2) / 2 := min_le_right _ _
    linarith
  have hzS : z ∈ S := by
    refine ⟨hz2, (hball ?_).le⟩
    rw [Real.dist_eq, abs_lt]
    have : min (ε / 2) ((sInf S - 2) / 2) ≤ ε / 2 := min_le_left _ _
    have : 0 < min (ε / 2) ((sInf S - 2) / 2) := lt_min (by linarith) (by linarith)
    constructor <;> linarith
  have := csInf_le hbdd hzS
  linarith

lemma logIntegralInv_ge {n : ℝ} (hn : 0 ≤ n) : 2 + n * Real.log 2 ≤ logIntegralInv n := by
  obtain ⟨h1, h2⟩ := logIntegral_logIntegralInv hn
  have h3 := logIntegral_le h2
  rw [h1] at h3
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog] at h3
  linarith

/-- `d/dx Li(x²) = x / log x`. -/
lemma hasDerivAt_logIntegral_sq {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => logIntegral (t ^ 2)) (x / Real.log x) x := by
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt logIntegral (1 / Real.log (x ^ 2)) (x ^ 2) := hasDerivAt_logIntegral hx2
  have h : HasDerivAt (fun t : ℝ => logIntegral (t ^ 2)) (1 / Real.log (x ^ 2) * (2 * x)) x :=
    HasDerivAt.comp (h := fun t : ℝ => t ^ 2) x h1 hp
  convert h using 1
  have hlog : Real.log (x ^ 2) = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [hlog]
  field_simp

end LandauRH

end

-- ===== LF7Q.lean =====
section

set_option autoImplicit false

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace LandauRH

open VonKoch LandauFunction ArithmeticFunction

/-! ### The weight `W(t) = t / log t` and its derivatives -/

/-- `W(t) = t / log t`. -/
def Wf (t : ℝ) : ℝ := t / Real.log t

/-- `w = W' = (log t - 1) / log² t`. -/
def wf (t : ℝ) : ℝ := (Real.log t - 1) / Real.log t ^ 2

/-- `w' = (2 - log t) / (t log³ t)`. -/
def wf' (t : ℝ) : ℝ := (2 - Real.log t) / (t * Real.log t ^ 3)

lemma hasDerivAt_Wf {t : ℝ} (ht : 1 < t) : HasDerivAt Wf (wf t) t := by
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have ht0 : t ≠ 0 := by linarith
  have h : HasDerivAt (fun x => x / Real.log x)
      ((1 * Real.log t - t * t⁻¹) / Real.log t ^ 2) t :=
    (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
  have e : (1 * Real.log t - t * t⁻¹) / Real.log t ^ 2 = wf t := by
    simp only [wf]; field_simp
  rw [e] at h
  exact h

lemma hasDerivAt_wf {t : ℝ} (ht : 1 < t) : HasDerivAt wf (wf' t) t := by
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have ht0 : t ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x => Real.log x - 1) t⁻¹ t := (Real.hasDerivAt_log ht0).sub_const 1
  have h2 : HasDerivAt (fun x => Real.log x ^ 2) ((2:ℕ) * Real.log t ^ (2 - 1) * t⁻¹) t :=
    (Real.hasDerivAt_log ht0).pow 2
  have h := h1.div h2 (pow_ne_zero 2 hl)
  have e : (t⁻¹ * Real.log t ^ 2 - (Real.log t - 1) * ((2:ℕ) * Real.log t ^ (2 - 1) * t⁻¹)) /
      (Real.log t ^ 2) ^ 2 = wf' t := by
    rw [wf']
    norm_num
    field_simp
    ring
  rw [e] at h
  exact h

lemma continuousOn_log_Ioi : ContinuousOn Real.log (Ioi 1) :=
  Real.continuousOn_log.mono (fun t (ht : 1 < t) => by
    simp only [mem_compl_iff, mem_singleton_iff]; linarith)

lemma log_ne_zero_of_one_lt {t : ℝ} (ht : 1 < t) : Real.log t ≠ 0 := (Real.log_pos ht).ne'

lemma continuousOn_wf : ContinuousOn wf (Ioi 1) := by
  refine ContinuousOn.div (continuousOn_log_Ioi.sub continuousOn_const)
    (continuousOn_log_Ioi.pow 2) (fun t ht => pow_ne_zero 2 (log_ne_zero_of_one_lt ht))

lemma continuousOn_wf' : ContinuousOn wf' (Ioi 1) := by
  refine ContinuousOn.div (continuousOn_const.sub continuousOn_log_Ioi)
    (continuousOn_id.mul (continuousOn_log_Ioi.pow 3)) (fun t ht => ?_)
  have ht' : (1:ℝ) < t := ht
  exact mul_ne_zero (show t ≠ 0 by linarith) (pow_ne_zero 3 (log_ne_zero_of_one_lt ht'))

lemma uIcc_subset_Ioi {a b : ℝ} (ha : 1 < a) (hb : 1 < b) : uIcc a b ⊆ Ioi 1 := by
  intro t ht
  have := ht.1
  simp only [mem_Ioi]
  exact lt_of_lt_of_le (lt_inf_iff.mpr ⟨ha, hb⟩) this

lemma intervalIntegrable_of_Ioi {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 1)) {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) : IntervalIntegrable f volume a b :=
  (hf.mono (uIcc_subset_Ioi ha hb)).intervalIntegrable

/-! ### `ψ₁` is continuous -/

lemma continuousOn_psi1 : ContinuousOn psi1 (Ioi 0) := by
  intro t ht
  set N : ℕ := ⌊t⌋₊ + 1
  have htN : t < N := by simp only [N]; push_cast; exact Nat.lt_floor_add_one t
  have hcont : Continuous (fun y : ℝ => ∑ n ∈ Finset.range N, Λ n * max (y - n) 0) := by
    fun_prop
  have heq : EqOn psi1 (fun y : ℝ => ∑ n ∈ Finset.range N, Λ n * max (y - n) 0) (Ioo 0 N) :=
    fun y hy => psi1_eq_sum_range hy.1.le hy.2
  exact ((hcont.continuousOn.congr heq).continuousAt
    (Ioo_mem_nhds ht htN)).continuousWithinAt

lemma continuousOn_psi1_Ioi1 : ContinuousOn psi1 (Ioi 1) :=
  continuousOn_psi1.mono (fun t (ht : 1 < t) => (show (0:ℝ) < t by linarith))

/-! ### Identity 1: `R_W(x) = ψ₁(x) w(x) - ∫₂ˣ ψ₁ w'` -/

/-- `R_W(x) = ∑_{n ≤ x} Λ(n) (W(x) - W(n))`. -/
def RW (x : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * (Wf x - Wf n)

lemma Wf_sub_eq {n x : ℝ} (hn : 2 ≤ n) (hnx : n ≤ x) :
    Wf x - Wf n = (x - n) * wf x - ∫ t in (2:ℝ)..x, max (t - n) 0 * wf' t := by
  have h1x : 1 < x := by linarith
  have hcont : ContinuousOn (fun t : ℝ => max (t - n) 0 * wf' t) (Ioi 1) :=
    (Continuous.continuousOn (by fun_prop : Continuous fun t : ℝ => max (t - n) 0)).mul
      continuousOn_wf'
  have hsplit : ∫ t in (2:ℝ)..x, max (t - n) 0 * wf' t = ∫ t in n..x, (t - n) * wf' t := by
    rw [← integral_add_adjacent_intervals (b := n)
      (intervalIntegrable_of_Ioi hcont (by norm_num) (by linarith))
      (intervalIntegrable_of_Ioi hcont (by linarith) h1x)]
    have e1 : ∫ t in (2:ℝ)..n, max (t - n) 0 * wf' t = 0 := by
      rw [integral_congr (g := fun _ => (0:ℝ)) (fun t ht => ?_)]
      · simp
      · rw [uIcc_of_le hn] at ht
        show max (t - n) 0 * wf' t = 0
        rw [max_eq_right (by linarith [ht.2]), zero_mul]
    have e2 : ∫ t in n..x, max (t - n) 0 * wf' t = ∫ t in n..x, (t - n) * wf' t := by
      refine integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hnx] at ht
      show max (t - n) 0 * wf' t = (t - n) * wf' t
      rw [max_eq_left (by linarith [ht.1])]
    rw [e1, e2, zero_add]
  have hibp := integral_mul_deriv_eq_deriv_mul (a := n) (b := x) (u := fun t => t - n)
    (u' := fun _ => (1:ℝ)) (v := wf) (v' := wf')
    (fun t _ => (hasDerivAt_id' t).sub_const n)
    (fun t ht => hasDerivAt_wf (uIcc_subset_Ioi (by linarith) h1x ht))
    intervalIntegrable_const
    (intervalIntegrable_of_Ioi continuousOn_wf' (by linarith) h1x)
  have hftc : ∫ t in n..x, wf t = Wf x - Wf n :=
    integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_Wf (uIcc_subset_Ioi (by linarith) h1x ht))
      (intervalIntegrable_of_Ioi continuousOn_wf (by linarith) h1x)
  simp only [one_mul, sub_self, zero_mul, sub_zero] at hibp
  rw [hsplit, hibp, hftc]
  ring

lemma RW_eq {x : ℝ} (hx : 2 ≤ x) :
    RW x = psi1 x * wf x - ∫ t in (2:ℝ)..x, psi1 t * wf' t := by
  set N := ⌊x⌋₊ + 1 with hN
  have hxN : x < N := by simp only [hN]; push_cast; exact Nat.lt_floor_add_one x
  have hterm : ∀ n ∈ Finset.range N, Λ n * (Wf x - Wf n) =
      Λ n * max (x - n) 0 * wf x - Λ n * ∫ t in (2:ℝ)..x, max (t - n) 0 * wf' t := by
    intro n hn
    by_cases hΛ : Λ n = 0
    · simp [hΛ]
    · have hn2 : 2 ≤ n := by
        by_contra h
        push Not at h
        interval_cases n <;> simp at hΛ
      have hnx : (n:ℝ) ≤ x := by
        have : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
      rw [Wf_sub_eq (by exact_mod_cast hn2) hnx, max_eq_left (by linarith)]
      ring
  rw [RW, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
  congr 1
  have hcont : ∀ n : ℕ, ContinuousOn (fun t : ℝ => Λ n * (max (t - n) 0 * wf' t)) (Ioi 1) :=
    fun n => continuousOn_const.mul
      ((Continuous.continuousOn (by fun_prop : Continuous fun t : ℝ => max (t - n) 0)).mul
        continuousOn_wf')
  have h1x : (1:ℝ) < x := by linarith
  calc ∑ n ∈ Finset.range N, Λ n * ∫ t in (2:ℝ)..x, max (t - n) 0 * wf' t
      = ∑ n ∈ Finset.range N, ∫ t in (2:ℝ)..x, Λ n * (max (t - n) 0 * wf' t) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in (2:ℝ)..x, ∑ n ∈ Finset.range N, Λ n * (max (t - n) 0 * wf' t) := by
        rw [intervalIntegral.integral_finsetSum]
        intro n _
        exact intervalIntegrable_of_Ioi (hcont n) (by norm_num) h1x
    _ = ∫ t in (2:ℝ)..x, psi1 t * wf' t := by
        refine integral_congr (fun t ht => ?_)
        rw [uIcc_of_le hx] at ht
        rw [psi1_eq_sum_range (by linarith [ht.1]) (lt_of_le_of_lt ht.2 hxN), Finset.sum_mul]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        ring

/-! ### Identity 2 -/

/-- `Φ(x) = x²/log x - Li(x²) - (x²/2) w(x) + ∫₂ˣ (t²/2) w'(t) dt` (constant). -/
def Phi8 (x : ℝ) : ℝ :=
  x ^ 2 / Real.log x - logIntegral (x ^ 2) - x ^ 2 / 2 * wf x + ∫ t in (2:ℝ)..x, t ^ 2 / 2 * wf' t

lemma continuousOn_sq_wf' : ContinuousOn (fun t : ℝ => t ^ 2 / 2 * wf' t) (Ioi 1) :=
  ((continuousOn_id.pow 2).div_const 2).mul continuousOn_wf'

lemma hasDerivAt_Phi8 {x : ℝ} (hx : 1 < x) : HasDerivAt Phi8 0 x := by
  have hl : Real.log x ≠ 0 := log_ne_zero_of_one_lt hx
  have hx0 : x ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t => t ^ 2 / Real.log t)
      (((2:ℕ) * x ^ (2 - 1) * 1 * Real.log x - x ^ 2 * x⁻¹) / Real.log x ^ 2) x :=
    ((hasDerivAt_id' x).pow 2).div (Real.hasDerivAt_log hx0) hl
  have h2 := hasDerivAt_logIntegral_sq hx
  have h3 : HasDerivAt (fun t => t ^ 2 / 2 * wf t)
      (((2:ℕ) * x ^ (2 - 1) * 1) / 2 * wf x + x ^ 2 / 2 * wf' x) x :=
    (((hasDerivAt_id' x).pow 2).div_const 2).mul (hasDerivAt_wf hx)
  have h4 : HasDerivAt (fun u => ∫ t in (2:ℝ)..u, t ^ 2 / 2 * wf' t) (x ^ 2 / 2 * wf' x) x :=
    integral_hasDerivAt_right (intervalIntegrable_of_Ioi continuousOn_sq_wf' (by norm_num) hx)
      (continuousOn_sq_wf'.stronglyMeasurableAtFilter isOpen_Ioi x hx)
      (continuousOn_sq_wf'.continuousAt (Ioi_mem_nhds hx))
  have h := ((h1.sub h2).sub h3).add h4
  have e : ((2:ℕ) * x ^ (2 - 1) * 1 * Real.log x - x ^ 2 * x⁻¹) / Real.log x ^ 2 -
      x / Real.log x - ((2:ℕ) * x ^ (2 - 1) * 1 / 2 * wf x + x ^ 2 / 2 * wf' x) +
      x ^ 2 / 2 * wf' x = 0 := by
    rw [wf]
    norm_num
    field_simp
    ring
  rw [e] at h
  exact h

lemma Phi8_eq {x : ℝ} (hx : 2 ≤ x) : Phi8 x = Phi8 2 := by
  have h := integral_eq_sub_of_hasDerivAt (f := Phi8) (f' := fun _ => (0:ℝ)) (a := 2) (b := x)
    (fun t ht => hasDerivAt_Phi8 (uIcc_subset_Ioi (by norm_num) (by linarith) ht))
    intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  linarith

/-- `D(t) = ψ₁(t) - t²/2`. -/
def Dfun (t : ℝ) : ℝ := psi1 t - t ^ 2 / 2

lemma continuousOn_Dfun : ContinuousOn Dfun (Ioi 1) :=
  continuousOn_psi1_Ioi1.sub ((continuousOn_id.pow 2).div_const 2)

lemma main_identity {x : ℝ} (hx : 2 ≤ x) :
    x ^ 2 / Real.log x - logIntegral (x ^ 2) - RW x =
      Phi8 2 - Dfun x * wf x + ∫ t in (2:ℝ)..x, Dfun t * wf' t := by
  have h1x : (1:ℝ) < x := by linarith
  rw [RW_eq hx, ← Phi8_eq hx, Phi8]
  have hI1 : IntervalIntegrable (fun t => psi1 t * wf' t) volume 2 x :=
    intervalIntegrable_of_Ioi (continuousOn_psi1_Ioi1.mul continuousOn_wf') (by norm_num) h1x
  have hI2 : IntervalIntegrable (fun t : ℝ => t ^ 2 / 2 * wf' t) volume 2 x :=
    intervalIntegrable_of_Ioi continuousOn_sq_wf' (by norm_num) h1x
  have e : ∫ t in (2:ℝ)..x, Dfun t * wf' t =
      (∫ t in (2:ℝ)..x, psi1 t * wf' t) - ∫ t in (2:ℝ)..x, t ^ 2 / 2 * wf' t := by
    rw [← integral_sub hI1 hI2]
    refine integral_congr (fun t _ => ?_)
    simp only [Dfun]
    ring
  rw [e, Dfun]
  ring

/-! ### Elementary bounds -/

lemma log_gt_069 {t : ℝ} (ht : 2 ≤ t) : 0.69 < Real.log t :=
  lt_of_lt_of_le (lt_trans (by norm_num) Real.log_two_gt_d9) (Real.log_le_log (by norm_num) ht)

lemma one_le_log_four_sq : 1 ≤ Real.log 4 ^ 2 := by
  have h : (4:ℝ) = 2 ^ 2 := by norm_num
  have h2 : Real.log 4 = 2 * Real.log 2 := by rw [h, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  rw [h2]; nlinarith

lemma abs_wf'_le {t : ℝ} (ht : 2 ≤ t) : |wf' t| ≤ 2 / (t * Real.log t ^ 2) := by
  have hl := log_gt_069 ht
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < Real.log t := by linarith
  rw [wf', abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 3),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h : |2 - Real.log t| ≤ 2 * Real.log t := by
    rw [abs_le]; constructor <;> linarith
  calc |2 - Real.log t| * (t * Real.log t ^ 2) ≤ 2 * Real.log t * (t * Real.log t ^ 2) := by
        gcongr
    _ = 2 * (t * Real.log t ^ 3) := by ring

lemma lam_wf_bounds {x : ℝ} (hx : 3 ≤ x) :
    0 ≤ Real.log x / x * wf x ∧ Real.log x / x * wf x ≤ 1 / x := by
  have hl : 1 ≤ Real.log x := one_le_log_of_three_le hx
  have hx0 : 0 < x := by linarith
  have e : Real.log x / x * wf x = (Real.log x - 1) / (x * Real.log x) := by
    rw [wf]; field_simp
  rw [e]
  constructor
  · apply div_nonneg (by linarith) (by positivity)
  · rw [div_le_div_iff₀ (by positivity) hx0]
    nlinarith

lemma rpow_three_halves_eq {t : ℝ} (ht : 0 < t) : t ^ (3/2:ℝ) = t * Real.sqrt t := by
  rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add ht, Real.rpow_one, Real.sqrt_eq_rpow]

lemma rpow_five_fourths_eq {t : ℝ} (ht : 0 < t) : t ^ (5/4:ℝ) = t * t ^ (1/4:ℝ) := by
  rw [show (5/4:ℝ) = 1 + 1/4 by norm_num, Real.rpow_add ht, Real.rpow_one]

lemma sqrt_sqrt_eq {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ (1/4:ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num

lemma sqrt_div_log_sq_le {t x : ℝ} (ht : 4 ≤ t) (htx : t ≤ x) :
    Real.sqrt t / Real.log t ^ 2 ≤
      x ^ (1/4:ℝ) / Real.log 4 ^ 2 + 4 * Real.sqrt x / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlt : Real.log 4 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hA : 0 ≤ x ^ (1/4:ℝ) / Real.log 4 ^ 2 := by positivity
  have hB : 0 ≤ 4 * Real.sqrt x / Real.log x ^ 2 := by positivity
  rcases le_total t (Real.sqrt x) with h | h
  · have h1 : Real.sqrt t ≤ x ^ (1/4:ℝ) := by
      rw [← sqrt_sqrt_eq hx0.le]; exact Real.sqrt_le_sqrt h
    have h2 : Real.sqrt t / Real.log t ^ 2 ≤ x ^ (1/4:ℝ) / Real.log 4 ^ 2 := by
      apply div_le_div₀ (by positivity) h1 (by positivity)
      exact pow_le_pow_left₀ hl4.le hlt 2
    linarith
  · have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hls : Real.log x / 2 ≤ Real.log t := by
      have : Real.log (Real.sqrt x) ≤ Real.log t := Real.log_le_log hsx h
      rw [Real.log_sqrt hx0.le] at this; exact this
    have h1 : Real.sqrt t ≤ Real.sqrt x := Real.sqrt_le_sqrt htx
    have h2 : Real.sqrt t / Real.log t ^ 2 ≤ Real.sqrt x / (Real.log x / 2) ^ 2 := by
      apply div_le_div₀ (by positivity) h1 (by positivity)
      exact pow_le_pow_left₀ (by positivity) hls 2
    have h3 : Real.sqrt x / (Real.log x / 2) ^ 2 = 4 * Real.sqrt x / Real.log x ^ 2 := by
      field_simp; ring
    linarith

/-- Pointwise bound for the integrand `D w'` on `[4, x]`. -/
lemma abs_D_wf'_le {S C t x : ℝ} (hC : 0 ≤ C) (ht : 4 ≤ t) (htx : t ≤ x)
    (hD : |Dfun t| ≤ S * t ^ (3/2:ℝ) + C * (t ^ (5/4:ℝ) * Real.log t ^ 2)) :
    |Dfun t * wf' t| ≤ 2 * |S| * (x ^ (1/4:ℝ) / Real.log 4 ^ 2 + 4 * Real.sqrt x /
      Real.log x ^ 2) + 2 * C * x ^ (1/4:ℝ) := by
  have ht0 : 0 < t := by linarith
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hw := abs_wf'_le (by linarith : (2:ℝ) ≤ t)
  rw [rpow_three_halves_eq ht0, rpow_five_fourths_eq ht0] at hD
  have hDn : 0 ≤ S * (t * Real.sqrt t) + C * (t * t ^ (1/4:ℝ) * Real.log t ^ 2) :=
    (abs_nonneg _).trans hD
  have h1 : |Dfun t * wf' t| ≤
      (S * (t * Real.sqrt t) + C * (t * t ^ (1/4:ℝ) * Real.log t ^ 2)) *
        (2 / (t * Real.log t ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul hD hw (abs_nonneg _) hDn
  have h2 : (S * (t * Real.sqrt t) + C * (t * t ^ (1/4:ℝ) * Real.log t ^ 2)) *
      (2 / (t * Real.log t ^ 2)) = 2 * S * (Real.sqrt t / Real.log t ^ 2) +
        2 * C * t ^ (1/4:ℝ) := by
    field_simp
  have h3 := sqrt_div_log_sq_le ht htx
  have h4 : 2 * S * (Real.sqrt t / Real.log t ^ 2) ≤ 2 * |S| * (Real.sqrt t / Real.log t ^ 2) := by
    have : S ≤ |S| := le_abs_self S
    have : 0 ≤ Real.sqrt t / Real.log t ^ 2 := by positivity
    nlinarith
  have h5 : 2 * |S| * (Real.sqrt t / Real.log t ^ 2) ≤ 2 * |S| * (x ^ (1/4:ℝ) / Real.log 4 ^ 2 +
      4 * Real.sqrt x / Real.log x ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : t ^ (1/4:ℝ) ≤ x ^ (1/4:ℝ) := Real.rpow_le_rpow ht0.le htx (by norm_num)
  have h7 : 2 * C * t ^ (1/4:ℝ) ≤ 2 * C * x ^ (1/4:ℝ) := mul_le_mul_of_nonneg_left h6 (by positivity)
  linarith

/-- Bound for `λ ∫₄ˣ D w'`. -/
lemma lam_integral_le {S C x : ℝ} (hC : 0 ≤ C) (hx : 4 ≤ x)
    (hD : ∀ t : ℝ, 4 ≤ t → |Dfun t| ≤ S * t ^ (3/2:ℝ) + C * (t ^ (5/4:ℝ) * Real.log t ^ 2)) :
    |Real.log x / x * ∫ t in (4:ℝ)..x, Dfun t * wf' t| ≤
      (2 * |S| + 2 * C) * (x ^ (1/4:ℝ) * Real.log x ^ 2) +
        8 * |S| * (Real.sqrt x / Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le (by linarith)
  set M := 2 * |S| * (x ^ (1/4:ℝ) / Real.log 4 ^ 2 + 4 * Real.sqrt x / Real.log x ^ 2) +
      2 * C * x ^ (1/4:ℝ) with hM
  have hI : ‖∫ t in (4:ℝ)..x, Dfun t * wf' t‖ ≤ M * |x - 4| := by
    refine norm_integral_le_of_norm_le_const (fun t ht => ?_)
    rw [uIoc_of_le hx] at ht
    rw [Real.norm_eq_abs]
    exact abs_D_wf'_le hC ht.1.le ht.2 (hD t ht.1.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - 4)] at hI
  have hM0 : 0 ≤ M := by positivity
  have hlam0 : 0 ≤ Real.log x / x := by positivity
  have h1 : |Real.log x / x * ∫ t in (4:ℝ)..x, Dfun t * wf' t| ≤ Real.log x * M := by
    rw [abs_mul, abs_of_nonneg hlam0]
    calc Real.log x / x * |∫ t in (4:ℝ)..x, Dfun t * wf' t| ≤ Real.log x / x * (M * x) := by
          apply mul_le_mul_of_nonneg_left _ hlam0
          nlinarith
      _ = Real.log x * M := by field_simp
  have h2 : Real.log x * M = 2 * |S| * (x ^ (1/4:ℝ) * Real.log x / Real.log 4 ^ 2) +
      8 * |S| * (Real.sqrt x / Real.log x) + 2 * C * (x ^ (1/4:ℝ) * Real.log x) := by
    rw [hM]; field_simp; ring
  have hq : 0 ≤ x ^ (1/4:ℝ) := by positivity
  have h4' : x ^ (1/4:ℝ) * Real.log x ≤ x ^ (1/4:ℝ) * Real.log x ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hq; nlinarith
  have h3 : x ^ (1/4:ℝ) * Real.log x / Real.log 4 ^ 2 ≤ x ^ (1/4:ℝ) * Real.log x ^ 2 :=
    (div_le_self (by positivity) one_le_log_four_sq).trans h4'
  have h4 : x ^ (1/4:ℝ) * Real.log x ≤ x ^ (1/4:ℝ) * Real.log x ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hq; nlinarith
  have hS : 0 ≤ |S| := abs_nonneg S
  have h5 : 2 * |S| * (x ^ (1/4:ℝ) * Real.log x / Real.log 4 ^ 2) ≤
      2 * |S| * (x ^ (1/4:ℝ) * Real.log x ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : 2 * C * (x ^ (1/4:ℝ) * Real.log x) ≤ 2 * C * (x ^ (1/4:ℝ) * Real.log x ^ 2) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  nlinarith

/-- Bound for `λ D(x) w(x)`. -/
lemma lam_D_wf_le {S C x : ℝ} (hx : 4 ≤ x)
    (hD : |Dfun x| ≤ S * x ^ (3/2:ℝ) + C * (x ^ (5/4:ℝ) * Real.log x ^ 2)) :
    Real.log x / x * (Dfun x * wf x) ≤ S * Real.sqrt x + C * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨h0, h1⟩ := lam_wf_bounds (by linarith : (3:ℝ) ≤ x)
  rw [rpow_three_halves_eq hx0, rpow_five_fourths_eq hx0] at hD
  have e : Real.log x / x * (Dfun x * wf x) = (Real.log x / x * wf x) * Dfun x := by ring
  rw [e]
  have hDle : Dfun x ≤ |Dfun x| := le_abs_self _
  have hDn : 0 ≤ |Dfun x| := abs_nonneg _
  calc (Real.log x / x * wf x) * Dfun x ≤ (Real.log x / x * wf x) * |Dfun x| :=
        mul_le_mul_of_nonneg_left hDle h0
    _ ≤ (1 / x) * |Dfun x| := mul_le_mul_of_nonneg_right h1 hDn
    _ ≤ (1 / x) * (S * (x * Real.sqrt x) + C * (x * x ^ (1/4:ℝ) * Real.log x ^ 2)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = S * Real.sqrt x + C * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by field_simp

/-- The integrated explicit-formula bound `|ψ₁(x) - x²/2| ≤ S★ x^{3/2} + C x^{5/4} log² x`. -/
def Psi1Bound : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 4 ≤ x →
    |psi1 x - x ^ 2 / 2| ≤ Sstar * x ^ (3/2 : ℝ) + C * (x ^ (5/4 : ℝ) * Real.log x ^ 2)

/-- **Lower bound for `Q_Λ`** (given the `ψ₁` bound). -/
theorem Q_lower (hP : Psi1Bound) : ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ x : ℝ, 4 ≤ x →
    -Sstar * Real.sqrt x - (K + C * (x ^ (1/4:ℝ) * Real.log x ^ 2) +
      8 * |Sstar| * (Real.sqrt x / Real.log x)) ≤
    Real.log x / x * (x ^ 2 / Real.log x - logIntegral (x ^ 2) - RW x) := by
  obtain ⟨C₀, hC₀, hD⟩ := hP
  have hD' : ∀ t : ℝ, 4 ≤ t →
      |Dfun t| ≤ Sstar * t ^ (3/2:ℝ) + C₀ * (t ^ (5/4:ℝ) * Real.log t ^ 2) := hD
  set I₀ := ∫ t in (2:ℝ)..4, Dfun t * wf' t with hI₀
  refine ⟨|Phi8 2| + |I₀|, 3 * C₀ + 2 * |Sstar|, by positivity,
    by have := abs_nonneg Sstar; linarith, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hcont : ContinuousOn (fun t => Dfun t * wf' t) (Ioi 1) := continuousOn_Dfun.mul continuousOn_wf'
  have hsplit : ∫ t in (2:ℝ)..x, Dfun t * wf' t = I₀ + ∫ t in (4:ℝ)..x, Dfun t * wf' t :=
    (integral_add_adjacent_intervals (intervalIntegrable_of_Ioi hcont (by norm_num) (by norm_num))
      (intervalIntegrable_of_Ioi hcont (by norm_num) (by linarith))).symm
  rw [main_identity (by linarith), hsplit]
  set J := ∫ t in (4:ℝ)..x, Dfun t * wf' t with hJ
  set lam := Real.log x / x with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (Real.log_nonneg (by linarith)) hx0.le
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one hx0]
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have ha : |lam * Phi8 2| ≤ |Phi8 2| := by
    rw [abs_mul, abs_of_nonneg hlam0]; exact mul_le_of_le_one_left (abs_nonneg _) hlam1
  have hc : |lam * I₀| ≤ |I₀| := by
    rw [abs_mul, abs_of_nonneg hlam0]; exact mul_le_of_le_one_left (abs_nonneg _) hlam1
  have hb := lam_D_wf_le hx (hD' x hx)
  have hd := lam_integral_le hC₀.le hx hD'
  rw [← hlam] at hb hd
  have e : lam * (Phi8 2 - Dfun x * wf x + (I₀ + J)) =
      lam * Phi8 2 - lam * (Dfun x * wf x) + lam * I₀ + lam * J := by ring
  rw [e]
  have ha' := neg_abs_le (lam * Phi8 2)
  have hc' := neg_abs_le (lam * I₀)
  have hd' := neg_abs_le (lam * J)
  nlinarith

end LandauRH

end

-- ===== LF7G.lean =====
section

set_option autoImplicit false

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace LandauRH

open VonKoch LandauFunction ArithmeticFunction

/-! ### `θ(t) = t + O(√t log² t)` under RH -/

/-- von Koch's bound `|ψ(x) - x| ≤ C √x log² x`. -/
def PsiBound : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2

lemma theta_error (hψ : PsiBound) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
    |Chebyshev.theta t - t| ≤ C * (Real.sqrt t * Real.log t ^ 2) := by
  obtain ⟨C₀, hC₀⟩ := hψ
  refine ⟨max C₀ 0 + 3, by positivity, fun t ht => ?_⟩
  have h1 := hC₀ t ht
  have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : (1:ℝ) ≤ t)
  have hl := log_gt_069 ht
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hq : 0 ≤ Real.sqrt t * Real.log t ^ 2 := by positivity
  have h3 : 2 * Real.sqrt t * Real.log t ≤ 3 * (Real.sqrt t * Real.log t ^ 2) := by
    have : 2 * Real.log t ≤ 3 * Real.log t ^ 2 := by nlinarith
    nlinarith
  have h4 : C₀ * Real.sqrt t * Real.log t ^ 2 ≤ max C₀ 0 * (Real.sqrt t * Real.log t ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hq
  have h5 : |Chebyshev.theta t - t| ≤ |Chebyshev.psi t - t| + |Chebyshev.psi t - Chebyshev.theta t| := by
    have := abs_sub (Chebyshev.psi t - t) (Chebyshev.psi t - Chebyshev.theta t)
    rw [show Chebyshev.psi t - t - (Chebyshev.psi t - Chebyshev.theta t) =
      Chebyshev.theta t - t by ring] at this
    exact this
  nlinarith

/-! ### Abel summation against `θ` -/

/-- `c(k) = log k` if `k` is prime, `0` otherwise. -/
def cθ (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

lemma sum_cθ_eq_theta (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cθ k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]; rfl

lemma abel_theta {f f' : ℝ → ℝ} {b : ℝ} (hb : 2 ≤ b)
    (hf : ∀ t ∈ Icc 2 b, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' (Icc 2 b)) :
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, f k * cθ k =
      f b * Chebyshev.theta b - ∫ t in (2:ℝ)..b, f' t * Chebyshev.theta t := by
  have hderiv : EqOn (deriv f) f' (Icc 2 b) := fun t ht => (hf t ht).deriv
  have hint : IntegrableOn (deriv f) (Icc 2 b) :=
    (hf'.integrableOn_Icc).congr_fun hderiv.symm measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ cθ (by simp [cθ]) (by simp [cθ]) b
    (fun t ht => (hf t ht).differentiableAt) hint
  rw [h, sum_cθ_eq_theta, integral_of_le hb]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  simp only [sum_cθ_eq_theta, hderiv (Ioc_subset_Icc_self ht)]

lemma sum_filter_prime_eq (m : ℕ) (g : ℕ → ℝ) :
    ∑ p ∈ (Finset.Ioc 0 m).filter Nat.Prime, g p =
      ∑ k ∈ Finset.Icc 0 m, (if k.Prime then g k else 0) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨⟨Nat.zero_le _, h⟩, hp⟩
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨⟨hp.pos, h⟩, hp⟩

lemma theta_lower {C₁ : ℝ}
    (hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ C₁ * (Real.sqrt t * Real.log t ^ 2))
    {t : ℝ} (ht : 2 ≤ t) : t - C₁ * (Real.sqrt t * Real.log t ^ 2) ≤ Chebyshev.theta t := by
  have := hθ t ht; rw [abs_le] at this; linarith

lemma theta_upper {C₁ : ℝ}
    (hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ C₁ * (Real.sqrt t * Real.log t ^ 2))
    {t : ℝ} (ht : 2 ≤ t) : Chebyshev.theta t ≤ t + C₁ * (Real.sqrt t * Real.log t ^ 2) := by
  have := hθ t ht; rw [abs_le] at this; linarith

lemma intervalIntegrable_mul_theta {g : ℝ → ℝ} {a b : ℝ} (hg : ContinuousOn g (uIcc a b)) :
    IntervalIntegrable (fun t => g t * Chebyshev.theta t) volume a b :=
  (Chebyshev.theta_mono.intervalIntegrable).continuousOn_mul hg

/-! ### The prime-square sum `P₂ = ∑_{p ≤ √x} (log p - λ p²/2)` -/

/-- `ω₂(t) = 1 - λ t² / (2 log t)`. -/
def om2 (lam t : ℝ) : ℝ := 1 - lam * (t ^ 2 / (2 * Real.log t))

/-- `-ω₂'(t) = λ (t / log t - t / (2 log² t))`. -/
def gm2 (lam t : ℝ) : ℝ := lam * (t / Real.log t - t / (2 * Real.log t ^ 2))

lemma hasDerivAt_om2 (lam : ℝ) {t : ℝ} (ht : 1 < t) : HasDerivAt (om2 lam) (-gm2 lam t) t := by
  have hl : Real.log t ≠ 0 := log_ne_zero_of_one_lt ht
  have ht0 : t ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x => x ^ 2 / (2 * Real.log x))
      (((2:ℕ) * t ^ (2 - 1) * 1 * (2 * Real.log t) - t ^ 2 * (2 * t⁻¹)) / (2 * Real.log t) ^ 2) t :=
    ((hasDerivAt_id' t).pow 2).div ((Real.hasDerivAt_log ht0).const_mul 2) (by positivity)
  have e2 : ((2:ℕ) * t ^ (2 - 1) * 1 * (2 * Real.log t) - t ^ 2 * (2 * t⁻¹)) /
      (2 * Real.log t) ^ 2 = t / Real.log t - t / (2 * Real.log t ^ 2) := by
    norm_num; field_simp
  rw [e2] at h1
  exact (h1.const_mul lam).const_sub 1

lemma continuousOn_gm2 (lam : ℝ) : ContinuousOn (gm2 lam) (Ioi 1) := by
  refine continuousOn_const.mul ((continuousOn_id.div continuousOn_log_Ioi
    (fun t ht => log_ne_zero_of_one_lt ht)).sub (continuousOn_id.div
      (continuousOn_const.mul (continuousOn_log_Ioi.pow 2)) (fun t ht => ?_)))
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (log_ne_zero_of_one_lt ht))

lemma om2_sqrt {x : ℝ} (hx : 1 < x) : om2 (Real.log x / x) (Real.sqrt x) = 0 := by
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≠ 0 := log_ne_zero_of_one_lt hx
  rw [om2, Real.sq_sqrt hx0.le, Real.log_sqrt hx0.le]
  field_simp
  ring

lemma T2_eq {x : ℝ} (hx : 4 ≤ x) :
    ∑ p ∈ (Finset.Ioc 0 ⌊Real.sqrt x⌋₊).filter Nat.Prime,
        (Real.log p - Real.log x / x * (p:ℝ) ^ 2 / 2) =
      ∫ t in (2:ℝ)..Real.sqrt x, gm2 (Real.log x / x) t * Chebyshev.theta t := by
  set lam := Real.log x / x with hlam
  have hY : 2 ≤ Real.sqrt x := by
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_le_sqrt hx
  rw [sum_filter_prime_eq]
  have hterm : ∀ k ∈ Finset.Icc 0 ⌊Real.sqrt x⌋₊,
      (if k.Prime then Real.log k - lam * (k:ℝ) ^ 2 / 2 else 0) = om2 lam k * cθ k := by
    intro k _
    by_cases hk : k.Prime
    · have hk1 : (1:ℝ) < k := by exact_mod_cast hk.one_lt
      have hl : Real.log k ≠ 0 := log_ne_zero_of_one_lt hk1
      rw [if_pos hk, cθ, if_pos hk, om2]
      field_simp
    · rw [if_neg hk, cθ, if_neg hk, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have h := abel_theta (f := om2 lam) (f' := fun t => -gm2 lam t) hY
    (fun t ht => hasDerivAt_om2 lam (by linarith [ht.1]))
    ((continuousOn_gm2 lam).neg.mono (fun t ht => by simp only [mem_Ioi]; linarith [ht.1]))
  rw [h, om2_sqrt (by linarith), zero_mul, zero_sub]
  rw [← intervalIntegral.integral_neg]
  refine integral_congr (fun t _ => ?_)
  ring

lemma sq_div_log_sq_le {t Y : ℝ} (ht : 2 ≤ t) (htY : t ≤ Y) :
    t ^ 2 / Real.log t ^ 2 ≤ Y / Real.log 2 ^ 2 + 4 * Y ^ 2 / Real.log Y ^ 2 := by
  have hY0 : 0 < Y := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hA : 0 ≤ Y / Real.log 2 ^ 2 := by positivity
  have hB : 0 ≤ 4 * Y ^ 2 / Real.log Y ^ 2 := by positivity
  rcases le_total t (Real.sqrt Y) with h | h
  · have h1 : t ^ 2 ≤ Y := by
      have := pow_le_pow_left₀ (by linarith) h 2
      rwa [Real.sq_sqrt hY0.le] at this
    have h2 : t ^ 2 / Real.log t ^ 2 ≤ Y / Real.log 2 ^ 2 := by
      apply div_le_div₀ hY0.le h1 (by positivity)
      exact pow_le_pow_left₀ hl2.le hlt 2
    linarith
  · have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
    have hls : Real.log Y / 2 ≤ Real.log t := by
      have : Real.log (Real.sqrt Y) ≤ Real.log t := Real.log_le_log hsY h
      rw [Real.log_sqrt hY0.le] at this; exact this
    have h1 : t ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (by linarith) htY 2
    have h2 : t ^ 2 / Real.log t ^ 2 ≤ Y ^ 2 / (Real.log Y / 2) ^ 2 := by
      apply div_le_div₀ (by positivity) h1 (by positivity)
      exact pow_le_pow_left₀ (by positivity) hls 2
    have h3 : Y ^ 2 / (Real.log Y / 2) ^ 2 = 4 * Y ^ 2 / Real.log Y ^ 2 := by
      field_simp; norm_num
    linarith

/-- The antiderivative `A(t) = t³ / (3 log t)` of `t²/log t - t²/(3 log² t)`. -/
def Acub (t : ℝ) : ℝ := t ^ 3 / (3 * Real.log t)

def acub (t : ℝ) : ℝ := t ^ 2 / Real.log t - t ^ 2 / (3 * Real.log t ^ 2)

lemma hasDerivAt_Acub {t : ℝ} (ht : 1 < t) : HasDerivAt Acub (acub t) t := by
  have hl : Real.log t ≠ 0 := log_ne_zero_of_one_lt ht
  have ht0 : t ≠ 0 := by linarith
  have h : HasDerivAt (fun x => x ^ 3 / (3 * Real.log x))
      (((3:ℕ) * t ^ (3 - 1) * 1 * (3 * Real.log t) - t ^ 3 * (3 * t⁻¹)) / (3 * Real.log t) ^ 2) t :=
    ((hasDerivAt_id' t).pow 3).div ((Real.hasDerivAt_log ht0).const_mul 3) (by positivity)
  have e : ((3:ℕ) * t ^ (3 - 1) * 1 * (3 * Real.log t) - t ^ 3 * (3 * t⁻¹)) /
      (3 * Real.log t) ^ 2 = acub t := by
    rw [acub]; norm_num; field_simp
  rw [e] at h
  exact h

lemma continuousOn_acub : ContinuousOn acub (Ioi 1) := by
  refine ((continuousOn_id.pow 2).div continuousOn_log_Ioi
    (fun t ht => log_ne_zero_of_one_lt ht)).sub ((continuousOn_id.pow 2).div
      (continuousOn_const.mul (continuousOn_log_Ioi.pow 2)) (fun t ht => ?_))
  exact mul_ne_zero three_ne_zero (pow_ne_zero 2 (log_ne_zero_of_one_lt ht))

/-- Pointwise lower bound for `gm2 · θ` on `[2, Y]`. -/
lemma gm2_theta_ge {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ C₁ * (Real.sqrt t * Real.log t ^ 2))
    {lam Y t : ℝ} (hlam : 0 ≤ lam) (ht : 2 ≤ t) (htY : t ≤ Y) :
    lam * acub t - (lam * (Y / Real.log 2 ^ 2 + 4 * Y ^ 2 / Real.log Y ^ 2) / 6 +
      C₁ * lam * (Y * Real.sqrt Y * Real.log Y)) ≤ gm2 lam t * Chebyshev.theta t := by
  have hl := log_gt_069 ht
  have hl0 : 0 < Real.log t := by linarith
  have ht0 : 0 < t := by linarith
  have hg0 : 0 ≤ gm2 lam t := by
    rw [gm2]
    apply mul_nonneg hlam
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) hl0]
    nlinarith [mul_nonneg (mul_nonneg ht0.le hl0.le) (by linarith : (0:ℝ) ≤ 2 * Real.log t - 1)]
  have hgle : gm2 lam t ≤ lam * (t / Real.log t) := by
    rw [gm2]
    apply mul_le_mul_of_nonneg_left _ hlam
    have : 0 ≤ t / (2 * Real.log t ^ 2) := by positivity
    linarith
  have hθl := theta_lower hθ ht
  have h1 : gm2 lam t * (t - C₁ * (Real.sqrt t * Real.log t ^ 2)) ≤ gm2 lam t * Chebyshev.theta t :=
    mul_le_mul_of_nonneg_left hθl hg0
  have h2 : gm2 lam t * t = lam * acub t - lam * (t ^ 2 / Real.log t ^ 2) / 6 := by
    rw [gm2, acub]; field_simp; ring
  have h3 : lam * (t ^ 2 / Real.log t ^ 2) / 6 ≤
      lam * (Y / Real.log 2 ^ 2 + 4 * Y ^ 2 / Real.log Y ^ 2) / 6 := by
    have := sq_div_log_sq_le ht htY
    have := mul_le_mul_of_nonneg_left this hlam
    linarith
  have hq : 0 ≤ C₁ * (Real.sqrt t * Real.log t ^ 2) := by positivity
  have h4 : gm2 lam t * (C₁ * (Real.sqrt t * Real.log t ^ 2)) ≤
      lam * (t / Real.log t) * (C₁ * (Real.sqrt t * Real.log t ^ 2)) :=
    mul_le_mul_of_nonneg_right hgle hq
  have h5 : lam * (t / Real.log t) * (C₁ * (Real.sqrt t * Real.log t ^ 2)) =
      C₁ * lam * (t * Real.sqrt t * Real.log t) := by
    field_simp
  have h6 : t * Real.sqrt t * Real.log t ≤ Y * Real.sqrt Y * Real.log Y := by
    have a1 : Real.sqrt t ≤ Real.sqrt Y := Real.sqrt_le_sqrt htY
    have a2 : Real.log t ≤ Real.log Y := Real.log_le_log ht0 htY
    have a3 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    have a4 : t * Real.sqrt t ≤ Y * Real.sqrt Y := mul_le_mul htY a1 a3 (by linarith)
    exact mul_le_mul a4 a2 hl0.le (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  have h7 : C₁ * lam * (t * Real.sqrt t * Real.log t) ≤ C₁ * lam * (Y * Real.sqrt Y * Real.log Y) :=
    mul_le_mul_of_nonneg_left h6 (mul_nonneg hC₁ hlam)
  have e : gm2 lam t * (t - C₁ * (Real.sqrt t * Real.log t ^ 2)) =
      gm2 lam t * t - gm2 lam t * (C₁ * (Real.sqrt t * Real.log t ^ 2)) := by ring
  rw [e, h2] at h1
  linarith

lemma sqrt_ge_four {x : ℝ} (hx : 16 ≤ x) : 4 ≤ Real.sqrt x := by
  rw [show (4:ℝ) = Real.sqrt 16 by
    rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
  exact Real.sqrt_le_sqrt hx

lemma lam_le_one {x : ℝ} (hx : 0 < x) : Real.log x / x ≤ 1 := by
  rw [div_le_one hx]; have := Real.log_le_sub_one_of_pos hx; linarith

/-- **Lower bound for `P₂`**. -/
lemma T2_lower {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ C₁ * (Real.sqrt t * Real.log t ^ 2))
    {x : ℝ} (hx : 16 ≤ x) :
    2 / 3 * Real.sqrt x - (4 + Real.log x + 8 / 3 * (Real.sqrt x / Real.log x) +
      C₁ * (x ^ (1/4:ℝ) * Real.log x ^ 2)) ≤
    ∑ p ∈ (Finset.Ioc 0 ⌊Real.sqrt x⌋₊).filter Nat.Prime,
        (Real.log p - Real.log x / x * (p:ℝ) ^ 2 / 2) := by
  have hx0 : 0 < x := by linarith
  have hY4 := sqrt_ge_four hx
  rw [T2_eq (by linarith)]
  set Y := Real.sqrt x with hYdef
  set lam := Real.log x / x with hlam
  have hY2 : Y ^ 2 = x := Real.sq_sqrt hx0.le
  have hYY : Y * Y = x := Real.mul_self_sqrt hx0.le
  have hlY : Real.log Y = Real.log x / 2 := Real.log_sqrt hx0.le
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlam0 : 0 ≤ lam := div_nonneg hlx.le hx0.le
  have hlam1 : lam ≤ 1 := lam_le_one hx0
  have hsY : Real.sqrt Y = x ^ (1/4:ℝ) := sqrt_sqrt_eq hx0.le
  set B := lam * (Y / Real.log 2 ^ 2 + 4 * Y ^ 2 / Real.log Y ^ 2) / 6 +
    C₁ * lam * (Y * Real.sqrt Y * Real.log Y) with hB
  have hcontA : ContinuousOn (fun t => lam * acub t - B) (Ioi 1) :=
    (continuousOn_const.mul continuousOn_acub).sub continuousOn_const
  have hmono : ∫ t in (2:ℝ)..Y, (lam * acub t - B) ≤
      ∫ t in (2:ℝ)..Y, gm2 lam t * Chebyshev.theta t :=
    integral_mono_on (by linarith) (intervalIntegrable_of_Ioi hcontA (by norm_num) (by linarith))
      (intervalIntegrable_mul_theta ((continuousOn_gm2 lam).mono
        (uIcc_subset_Ioi (by norm_num) (by linarith))))
      (fun t ht => gm2_theta_ge hC₁ hθ hlam0 ht.1 ht.2)
  have hIa : IntervalIntegrable (fun t => lam * acub t) volume 2 Y :=
    intervalIntegrable_of_Ioi (continuousOn_const.mul continuousOn_acub) (by norm_num) (by linarith)
  have hcalc : ∫ t in (2:ℝ)..Y, (lam * acub t - B) = lam * (Acub Y - Acub 2) - B * (Y - 2) := by
    rw [intervalIntegral.integral_sub hIa intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      integral_eq_sub_of_hasDerivAt
        (fun t ht => hasDerivAt_Acub (uIcc_subset_Ioi (by norm_num) (by linarith) ht))
        (intervalIntegrable_of_Ioi continuousOn_acub (by norm_num) (by linarith)),
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hA : lam * Acub Y = 2 / 3 * Y := by
    have e : Y ^ 3 = Y * x := by rw [← hY2]; ring
    rw [hlam, Acub, hlY, e]
    field_simp
  have hA2 : lam * Acub 2 ≤ 4 := by
    have hl2 := Real.log_two_gt_d9
    have hAc : Acub 2 = 8 / (3 * Real.log 2) := by rw [Acub]; norm_num
    have h0 : 0 ≤ Acub 2 := by rw [hAc]; positivity
    have h1 : Acub 2 ≤ 4 := by
      rw [hAc, div_le_iff₀ (by positivity)]; linarith
    calc lam * Acub 2 ≤ 1 * Acub 2 := mul_le_mul_of_nonneg_right hlam1 h0
      _ ≤ 4 := by linarith
  have hB0 : 0 ≤ B := by
    have hlY0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
    have b1 : 0 ≤ lam * (Y / Real.log 2 ^ 2 + 4 * Y ^ 2 / Real.log Y ^ 2) / 6 :=
      div_nonneg (mul_nonneg hlam0 (add_nonneg (div_nonneg (by linarith) (sq_nonneg _))
        (div_nonneg (by positivity) (sq_nonneg _)))) (by norm_num)
    have b2 : 0 ≤ C₁ * lam * (Y * Real.sqrt Y * Real.log Y) :=
      mul_nonneg (mul_nonneg hC₁ hlam0) (mul_nonneg (mul_nonneg (by linarith)
        (Real.sqrt_nonneg _)) hlY0)
    rw [hB]; linarith
  have hBY : B * (Y - 2) ≤ B * Y := by nlinarith
  have e1 : lam * (Y / Real.log 2 ^ 2) / 6 * Y = Real.log x / (6 * Real.log 2 ^ 2) := by
    rw [hlam]
    have : Y / Real.log 2 ^ 2 / 6 * Y = (Y * Y) / (6 * Real.log 2 ^ 2) := by ring
    rw [mul_div_assoc, show Real.log x / x * (Y / Real.log 2 ^ 2 / 6) * Y =
      Real.log x / x * (Y / Real.log 2 ^ 2 / 6 * Y) by ring, this, hYY]
    field_simp
  have e2 : lam * (4 * Y ^ 2 / Real.log Y ^ 2) / 6 * Y = 8 / 3 * (Y / Real.log x) := by
    rw [hlam, hY2, hlY]
    field_simp
    ring
  have e3 : C₁ * lam * (Y * Real.sqrt Y * Real.log Y) * Y =
      C₁ / 2 * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by
    calc C₁ * lam * (Y * Real.sqrt Y * Real.log Y) * Y =
        C₁ * lam * (Y * Y) * Real.sqrt Y * Real.log Y := by ring
      _ = C₁ * (Real.log x / x) * x * x ^ (1/4:ℝ) * (Real.log x / 2) := by rw [hYY, hsY, hlY]
      _ = C₁ / 2 * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by field_simp
  have hBY' : B * Y = Real.log x / (6 * Real.log 2 ^ 2) + 8 / 3 * (Y / Real.log x) +
      C₁ / 2 * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by
    rw [← e1, ← e2, ← e3, hB]; ring
  have hl6 : Real.log x / (6 * Real.log 2 ^ 2) ≤ Real.log x := by
    have hl2 := Real.log_two_gt_d9
    apply div_le_self hlx.le
    nlinarith
  have hq : 0 ≤ C₁ / 2 * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by positivity
  have hq2 : C₁ / 2 * (x ^ (1/4:ℝ) * Real.log x ^ 2) ≤ C₁ * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by
    have : 0 ≤ C₁ * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by positivity
    linarith
  linarith

/-! ### The `j = 2` part of `M(x)` -/

/-- `ω̃₀(t) = 1 - 2 (t - 1)² / x`. -/
def om0 (x t : ℝ) : ℝ := 1 - 2 * (t - 1) ^ 2 / x

lemma hasDerivAt_om0 (x t : ℝ) : HasDerivAt (om0 x) (-(4 * (t - 1) / x)) t := by
  have h : HasDerivAt (fun s : ℝ => 1 - 2 * (s - 1) ^ 2 / x)
      (-(2 * ((2:ℕ) * (t - 1) ^ (2 - 1) * 1) / x)) t :=
    ((((hasDerivAt_id' t).sub_const 1).pow 2).const_mul 2 |>.div_const x).const_sub 1
  have e : -(2 * ((2:ℕ) * (t - 1) ^ (2 - 1) * 1) / x) = -(4 * (t - 1) / x) := by
    norm_num; ring
  rw [e] at h
  exact h

lemma Delta_two_le_om0 {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) (hpx : (p:ℝ) ≤ Real.sqrt x) :
    Delta x p 2 ≤ om0 x p * Real.log p := by
  have hx0 : 0 < x := by linarith
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0:ℝ) < p := by linarith
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have h2l : 2 * Real.log p ≤ Real.log x := by
    have := Real.log_le_log hp0 hpx
    rw [Real.log_sqrt hx0.le] at this; linarith
  have hincr : incr p 2 = (p:ℝ) ^ 2 - p := by simp [incr]
  rw [Delta, hincr, om0]
  have key : 2 * (p - 1) ^ 2 * Real.log p ≤ Real.log x * ((p:ℝ) ^ 2 - p) := by
    have a1 : 2 * Real.log p * (p - 1) ^ 2 ≤ Real.log x * (p - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right h2l (sq_nonneg _)
    have a2 : Real.log x * ((p:ℝ) - 1) ^ 2 ≤ Real.log x * ((p:ℝ) ^ 2 - p) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hlx
    nlinarith
  have : 2 * ((p:ℝ) - 1) ^ 2 / x * Real.log p ≤ Real.log x / x * ((p:ℝ) ^ 2 - p) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right key hx0.le
  nlinarith

lemma Delta_two_nonpos_of_gt {x : ℝ} (hx : 4 ≤ x) {p : ℕ} (hpx : Real.sqrt x < (p:ℝ)) :
    Delta x p 2 ≤ 0 := by
  have hx0 : 0 < x := by linarith
  set s := Real.sqrt x with hs
  have hs2 : 2 ≤ s := by
    rw [hs, show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_le_sqrt hx
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hp0 : 0 < (p:ℝ) := by linarith
  have hlx : 1 ≤ Real.log x := one_le_log_of_three_le (by linarith)
  have hincr : incr p 2 = (p:ℝ) ^ 2 - p := by simp [incr]
  rw [Delta, hincr]
  -- log p = log s + log (p/s) ≤ log x / 2 + (p - s)/s
  have hlogp : Real.log p ≤ Real.log x / 2 + (p - s) / s := by
    have e : Real.log p = Real.log s + Real.log (p / s) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h1 : Real.log (p / s) ≤ p / s - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log s = Real.log x / 2 := Real.log_sqrt hx0.le
    have h3 : (p:ℝ) / s - 1 = (p - s) / s := by field_simp
    linarith
  set L := Real.log x with hL
  clear_value L
  have key : L / 2 + (p - s) / s ≤ L / x * ((p:ℝ) ^ 2 - p) := by
    rw [← hss]
    have hs0 : 0 < s := by linarith
    rw [div_add_div _ _ (two_ne_zero) hs0.ne', div_mul_eq_mul_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hps : 0 < (p:ℝ) - s := by linarith
    have hnum : 0 ≤ 2 * L * ((p:ℝ) ^ 2 - p) - L * s ^ 2 - 2 * ((p:ℝ) - s) * s := by
      have b1 : 0 ≤ L * (2 * ((p:ℝ) - s) * (p - s / 2) + p * (s - 2)) :=
        mul_nonneg (by linarith) (by nlinarith)
      have b2 : 0 ≤ 2 * (L - 1) * (((p:ℝ) - s) * s) := by
        have := mul_nonneg (by linarith : 0 ≤ L - 1) (mul_nonneg hps.le hs0.le); linarith
      nlinarith [b1, b2]
    nlinarith [mul_nonneg hs0.le hnum]
  linarith

lemma om0_Y1 {x : ℝ} (hx : 0 < x) : om0 x (1 + Real.sqrt (x / 2)) = 0 := by
  rw [om0, add_sub_cancel_left, Real.sq_sqrt (by positivity)]; field_simp; ring

lemma sqrt_two_mul_sqrt_half {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt 2 * Real.sqrt (x / 2) = Real.sqrt x := by
  rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring

lemma Y1_le_sqrt {x : ℝ} (hx : 16 ≤ x) : 1 + Real.sqrt (x / 2) ≤ Real.sqrt x := by
  have h4 := sqrt_ge_four hx
  have h2 : (1.41:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt (x / 2) := Real.sqrt_nonneg _
  have he := sqrt_two_mul_sqrt_half (by linarith : (0:ℝ) ≤ x)
  have : 1.41 * Real.sqrt (x / 2) ≤ Real.sqrt x := by nlinarith
  linarith

lemma two_le_Y1 {x : ℝ} (hx : 2 ≤ x) : 2 ≤ 1 + Real.sqrt (x / 2) := by
  have : 1 ≤ Real.sqrt (x / 2) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  linarith

lemma M2_abel {x : ℝ} (hx : 16 ≤ x) :
    ∑ k ∈ Finset.Icc 0 ⌊1 + Real.sqrt (x / 2)⌋₊, om0 x k * cθ k =
      ∫ t in (2:ℝ)..(1 + Real.sqrt (x / 2)), 4 * (t - 1) / x * Chebyshev.theta t := by
  have hx0 : 0 < x := by linarith
  have h := abel_theta (f := om0 x) (f' := fun t => -(4 * (t - 1) / x))
    (two_le_Y1 (by linarith)) (fun t _ => hasDerivAt_om0 x t)
    (Continuous.continuousOn (by fun_prop))
  rw [h, om0_Y1 hx0, zero_mul, zero_sub, ← intervalIntegral.integral_neg]
  refine integral_congr (fun t _ => ?_)
  ring

lemma M2_integral_le {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ C₁ * (Real.sqrt t * Real.log t ^ 2))
    {x : ℝ} (hx : 16 ≤ x) :
    ∫ t in (2:ℝ)..(1 + Real.sqrt (x / 2)), 4 * (t - 1) / x * Chebyshev.theta t ≤
      Real.sqrt 2 / 3 * Real.sqrt x + 1 + C₁ * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  set Y₁ := 1 + Real.sqrt (x / 2) with hY₁
  have hY₁2 : 2 ≤ Y₁ := two_le_Y1 (by linarith)
  have hY₁x : Y₁ ≤ Real.sqrt x := Y1_le_sqrt hx
  set E₁ := 4 / x * C₁ * (Y₁ * (Real.sqrt Y₁ * Real.log Y₁ ^ 2)) with hE₁
  have hpt : ∀ t ∈ Icc (2:ℝ) Y₁, 4 * (t - 1) / x * Chebyshev.theta t ≤
      4 / x * (t ^ 2 - t) + E₁ := by
    intro t ht
    have ht2 := ht.1
    have htY := ht.2
    have ht0 : 0 < t := by linarith
    have hθu := theta_upper hθ ht2
    have hc : 0 ≤ 4 * (t - 1) / x := by apply div_nonneg _ hx0.le; linarith
    have h1 : 4 * (t - 1) / x * Chebyshev.theta t ≤
        4 * (t - 1) / x * (t + C₁ * (Real.sqrt t * Real.log t ^ 2)) :=
      mul_le_mul_of_nonneg_left hθu hc
    have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have h2 : Real.sqrt t * Real.log t ^ 2 ≤ Real.sqrt Y₁ * Real.log Y₁ ^ 2 :=
      mul_le_mul (Real.sqrt_le_sqrt htY) (pow_le_pow_left₀ hlt (Real.log_le_log ht0 htY) 2)
        (by positivity) (Real.sqrt_nonneg _)
    have h3 : (t - 1) * (Real.sqrt t * Real.log t ^ 2) ≤ Y₁ * (Real.sqrt Y₁ * Real.log Y₁ ^ 2) :=
      mul_le_mul (by linarith) h2 (by positivity) (by linarith)
    have h4 : 4 * (t - 1) / x * (C₁ * (Real.sqrt t * Real.log t ^ 2)) =
        4 / x * C₁ * ((t - 1) * (Real.sqrt t * Real.log t ^ 2)) := by ring
    have h5 : 4 / x * C₁ * ((t - 1) * (Real.sqrt t * Real.log t ^ 2)) ≤ E₁ :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h6 : 4 * (t - 1) / x * (t + C₁ * (Real.sqrt t * Real.log t ^ 2)) =
        4 / x * (t ^ 2 - t) + 4 * (t - 1) / x * (C₁ * (Real.sqrt t * Real.log t ^ 2)) := by ring
    linarith
  have hI1 : IntervalIntegrable (fun t => 4 * (t - 1) / x * Chebyshev.theta t) volume 2 Y₁ :=
    intervalIntegrable_mul_theta (Continuous.continuousOn (by fun_prop))
  have hI2 : IntervalIntegrable (fun t : ℝ => 4 / x * (t ^ 2 - t) + E₁) volume 2 Y₁ :=
    (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  have hmono := integral_mono_on (by linarith) hI1 hI2 hpt
  have hF : ∀ t ∈ uIcc (2:ℝ) Y₁, HasDerivAt (fun t : ℝ => t ^ 3 / 3 - t ^ 2 / 2) (t ^ 2 - t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t ^ 3 / 3) (((3:ℕ):ℝ) * t ^ (3 - 1) * 1 / 3) t :=
      ((hasDerivAt_id' t).pow 3).div_const 3
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (((2:ℕ):ℝ) * t ^ (2 - 1) * 1 / 2) t :=
      ((hasDerivAt_id' t).pow 2).div_const 2
    have h := h1.sub h2
    have e : ((3:ℕ):ℝ) * t ^ (3 - 1) * 1 / 3 - ((2:ℕ):ℝ) * t ^ (2 - 1) * 1 / 2 = t ^ 2 - t := by
      norm_num
    rw [e] at h
    exact h
  have hcalc : ∫ t in (2:ℝ)..Y₁, (4 / x * (t ^ 2 - t) + E₁) =
      4 / x * ((Y₁ ^ 3 / 3 - Y₁ ^ 2 / 2) - (2 ^ 3 / 3 - 2 ^ 2 / 2)) + E₁ * (Y₁ - 2) := by
    rw [intervalIntegral.integral_add
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      integral_eq_sub_of_hasDerivAt hF ((Continuous.continuousOn (by fun_prop)).intervalIntegrable),
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hcalc] at hmono
  -- numerics
  set s := Real.sqrt (x / 2) with hs
  have hs2 : s ^ 2 = x / 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss := sqrt_two_mul_sqrt_half hx0.le
  rw [← hs] at hss
  have hmain : 4 / x * ((Y₁ ^ 3 / 3 - Y₁ ^ 2 / 2) - (2 ^ 3 / 3 - 2 ^ 2 / 2)) =
      2 * s / 3 + 1 - 10 / (3 * x) := by
    rw [hY₁]
    have e : (1 + s) ^ 3 / 3 - (1 + s) ^ 2 / 2 - (2 ^ 3 / 3 - 2 ^ 2 / 2) =
        s * s ^ 2 / 3 + s ^ 2 / 2 - 5 / 6 := by ring
    rw [e, hs2]
    field_simp
    ring
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hmain2 : 2 * s / 3 = Real.sqrt 2 / 3 * Real.sqrt x := by
    rw [← hss]
    have : Real.sqrt 2 / 3 * (Real.sqrt 2 * s) = (Real.sqrt 2 * Real.sqrt 2) * s / 3 := by ring
    rw [this, hsq2]
  have h10 : 0 ≤ 10 / (3 * x) := by positivity
  -- error term
  have hY₁0 : 0 < Y₁ := by linarith
  have hlY₁ : 0 ≤ Real.log Y₁ := Real.log_nonneg (by linarith)
  have hlY₁x : Real.log Y₁ ≤ Real.log x / 2 := by
    have := Real.log_le_log hY₁0 hY₁x
    rwa [Real.log_sqrt hx0.le] at this
  have hYsq : Y₁ * Y₁ ≤ x := by
    have := mul_le_mul hY₁x hY₁x hY₁0.le (Real.sqrt_nonneg _)
    rwa [Real.mul_self_sqrt hx0.le] at this
  have hsY : Real.sqrt Y₁ ≤ x ^ (1/4:ℝ) := by
    rw [← sqrt_sqrt_eq hx0.le]; exact Real.sqrt_le_sqrt hY₁x
  have hlog2 : Real.log Y₁ ^ 2 ≤ Real.log x ^ 2 / 4 := by
    have := pow_le_pow_left₀ hlY₁ hlY₁x 2
    have e : (Real.log x / 2) ^ 2 = Real.log x ^ 2 / 4 := by ring
    linarith
  have hE0 : 0 ≤ E₁ := by positivity
  have hE : E₁ * (Y₁ - 2) ≤ C₁ * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by
    have a1 : E₁ * (Y₁ - 2) ≤ E₁ * Y₁ := by nlinarith
    have a2 : E₁ * Y₁ = 4 / x * C₁ * ((Y₁ * Y₁) * (Real.sqrt Y₁ * Real.log Y₁ ^ 2)) := by
      rw [hE₁]; ring
    have a3 : (Y₁ * Y₁) * (Real.sqrt Y₁ * Real.log Y₁ ^ 2) ≤
        x * (x ^ (1/4:ℝ) * (Real.log x ^ 2 / 4)) := by
      apply mul_le_mul hYsq _ (by positivity) hx0.le
      exact mul_le_mul hsY hlog2 (by positivity) (by positivity)
    have a4 : 4 / x * C₁ * ((Y₁ * Y₁) * (Real.sqrt Y₁ * Real.log Y₁ ^ 2)) ≤
        4 / x * C₁ * (x * (x ^ (1/4:ℝ) * (Real.log x ^ 2 / 4))) :=
      mul_le_mul_of_nonneg_left a3 (by positivity)
    have a5 : 4 / x * C₁ * (x * (x ^ (1/4:ℝ) * (Real.log x ^ 2 / 4))) =
        C₁ * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by field_simp
    linarith
  linarith

lemma om0_nonneg {x : ℝ} (hx : 0 < x) {t : ℝ} (ht1 : 1 ≤ t) (ht : t ≤ 1 + Real.sqrt (x / 2)) :
    0 ≤ om0 x t := by
  have hs2 : Real.sqrt (x / 2) ^ 2 = x / 2 := Real.sq_sqrt (by positivity)
  have h1 : (t - 1) ^ 2 ≤ x / 2 := by
    rw [← hs2]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [om0, sub_nonneg, div_le_one hx]
  linarith

lemma om0_neg {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 1 + Real.sqrt (x / 2) < t) : om0 x t < 0 := by
  have hs2 : Real.sqrt (x / 2) ^ 2 = x / 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (x / 2) := Real.sqrt_nonneg _
  have h1 : x / 2 < (t - 1) ^ 2 := by
    rw [← hs2]; exact pow_lt_pow_left₀ (by linarith) hs0 two_ne_zero
  rw [om0, sub_neg, lt_div_iff₀ hx]
  linarith

/-- **Upper bound for the `j = 2` part of `M(x)`**. -/
lemma M2_upper {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ C₁ * (Real.sqrt t * Real.log t ^ 2))
    {x : ℝ} (hx : 16 ≤ x) :
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, max 0 (Delta x p 2) ≤
      Real.sqrt 2 / 3 * Real.sqrt x + 1 + C₁ * (x ^ (1/4:ℝ) * Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  set Y₁ := 1 + Real.sqrt (x / 2) with hY₁
  have hY₁2 : 2 ≤ Y₁ := two_le_Y1 (by linarith)
  have hY₁x : Y₁ ≤ Real.sqrt x := Y1_le_sqrt hx
  have hsx : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set m := ⌊Y₁⌋₊ with hm
  have hmN : m ≤ ⌊x⌋₊ := Nat.floor_le_floor (hY₁x.trans hsx)
  have hset : (Finset.range (⌊x⌋₊ + 1)).filter (fun k => k ≤ m) = Finset.Icc 0 m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨_, h⟩; exact ⟨Nat.zero_le _, h⟩
    · rintro ⟨_, h⟩; exact ⟨by omega, h⟩
  have hterm : ∀ p ∈ Finset.range (⌊x⌋₊ + 1),
      (if p.Prime then max 0 (Delta x p 2) else 0) ≤ (if p ≤ m then om0 x p * cθ p else 0) := by
    intro p _
    by_cases hp : p.Prime
    · have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      rw [if_pos hp]
      by_cases hpm : p ≤ m
      · rw [if_pos hpm, cθ, if_pos hp]
        have hpY : (p:ℝ) ≤ Y₁ := (Nat.cast_le.mpr hpm).trans (Nat.floor_le (by linarith))
        exact max_le (mul_nonneg (om0_nonneg hx0 hp1 hpY) hlp.le)
          (Delta_two_le_om0 (by linarith) hp (hpY.trans hY₁x))
      · rw [if_neg hpm]
        have hpY : Y₁ < (p:ℝ) := (Nat.floor_lt (by linarith)).mp (not_le.mp hpm)
        refine max_le le_rfl ?_
        rcases le_or_gt (p:ℝ) (Real.sqrt x) with h | h
        · have h1 := Delta_two_le_om0 (by linarith) hp h
          have h2 := om0_neg hx0 hpY
          nlinarith
        · exact Delta_two_nonpos_of_gt (by linarith) h
    · rw [if_neg hp]
      split_ifs
      · rw [cθ, if_neg hp, mul_zero]
      · exact le_rfl
  have h1 : ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, max 0 (Delta x p 2) ≤
      ∑ k ∈ Finset.Icc 0 m, om0 x k * cθ k := by
    rw [Finset.sum_filter, ← hset, Finset.sum_filter]
    exact Finset.sum_le_sum hterm
  rw [hm, M2_abel hx] at h1
  exact h1.trans (M2_integral_le hC₁ hθ hx)

/-! ### Decomposition of `λ R_W(x)` into prime powers -/

lemma lam_RW_eq {x : ℝ} (hx : 1 < x) :
    Real.log x / x * RW x =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * (1 - Real.log x / x * Wf n) := by
  rw [RW, Finset.mul_sum]
  have hx0 : x ≠ 0 := by linarith
  have h : Real.log x / x * Wf x = 1 := by
    rw [Wf]; field_simp [log_ne_zero_of_one_lt hx]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have e : Real.log x / x * (Λ n * (Wf x - Wf n)) =
      Λ n * (Real.log x / x * Wf x - Real.log x / x * Wf n) := by ring
  rw [e, h]

lemma sum_vonMangoldt_eq {x : ℝ} (hx : 1 ≤ x) (F : ℕ → ℝ) :
    ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * F n =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1:ℝ) / k)⌋₊).filter Nat.Prime, Real.log p * F (p ^ k) := by
  have h0 : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n * F n =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * F n := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      simp only [Finset.mem_range]; omega
    · intro n hn hn'
      have : n = 0 := by
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Ioc, not_and, not_le] at hn'
        by_contra h
        have := hn' (Nat.pos_of_ne_zero h)
        omega
      subst this; simp
  rw [← h0, ← Finset.sum_filter_of_ne (p := IsPrimePow)]
  · rw [Chebyshev.sum_PrimePow_eq_sum_sum (fun n => Λ n * F n) (by linarith)]
    refine Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun p hp => ?_))
    have hk1 : k ≠ 0 := by
      simp only [Finset.mem_Icc] at hk; omega
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    rw [vonMangoldt_apply_pow hk1, vonMangoldt_apply_prime hpp]
  · intro n _ hn
    have : Λ n ≠ 0 := left_ne_zero_of_mul hn
    by_contra h
    exact this (vonMangoldt_eq_zero_iff.mpr h)

lemma term_eq (lam : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    Real.log p * (1 - lam * Wf ((p ^ k : ℕ) : ℝ)) = Real.log p - lam * (p:ℝ) ^ k / k := by
  have hl : Real.log p ≠ 0 := log_ne_zero_of_one_lt (by exact_mod_cast hp.one_lt)
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  rw [Wf, Nat.cast_pow, Real.log_pow]
  field_simp

/-- `T_k = ∑_{p ≤ x^{1/k}} (log p - λ p^k / k)`. -/
def Tk (x : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1:ℝ) / k)⌋₊).filter Nat.Prime,
    (Real.log p - Real.log x / x * (p:ℝ) ^ k / k)

lemma lam_RW_eq_sum_Tk {x : ℝ} (hx : 1 < x) :
    Real.log x / x * RW x = ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, Tk x k := by
  rw [lam_RW_eq hx, sum_vonMangoldt_eq hx.le]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk1 : k ≠ 0 := by simp only [Finset.mem_Icc] at hk; omega
  rw [Tk]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  exact term_eq _ (Finset.mem_filter.mp hp).2 hk1

lemma sum_Icc_one_split (f : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, f k = f 1 + f 2 + ∑ k ∈ Finset.Icc 3 N, f k := by
  have h1 : Finset.Icc 1 N = {1, 2} ∪ Finset.Icc 3 N := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]; omega
  have hd : Disjoint ({1, 2} : Finset ℕ) (Finset.Icc 3 N) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [Finset.mem_Icc] at hk'
    omega
  rw [h1, Finset.sum_union hd, Finset.sum_pair (by norm_num)]

lemma log_div_log_two_ge_two {x : ℝ} (hx : 4 ≤ x) : 2 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
  apply Nat.le_floor
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  push_cast; linarith

lemma floor_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    (⌊Real.log x / Real.log 2⌋₊ : ℝ) ≤ 2 * Real.log x := by
  have hl2 := Real.log_two_gt_d9
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : (⌊Real.log x / Real.log 2⌋₊ : ℝ) ≤ Real.log x / Real.log 2 :=
    Nat.floor_le (div_nonneg hlx (by linarith))
  have h2 : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-! ### The `k ≥ 3` terms -/

lemma Tk_ge {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : 3 ≤ k) :
    -(x ^ (1/3:ℝ) * Real.log x) ≤ Tk x k := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k:ℝ) ≠ 0 := by linarith
  have hk1 : (1:ℝ) ≤ k := by linarith
  set S := (Finset.Ioc 0 ⌊x ^ ((1:ℝ) / k)⌋₊).filter Nat.Prime with hS
  have hterm : ∀ p ∈ S, -Real.log x ≤ Real.log p - Real.log x / x * (p:ℝ) ^ k / k := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hple : p ≤ ⌊x ^ ((1:ℝ) / k)⌋₊ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    have hpx : (p:ℝ) ≤ x ^ ((1:ℝ) / k) :=
      (Nat.cast_le.mpr hple).trans (Nat.floor_le (by positivity))
    have hpk : (p:ℝ) ^ k ≤ x := by
      have h1 : (p:ℝ) ^ k ≤ (x ^ ((1:ℝ) / k)) ^ k := pow_le_pow_left₀ (by positivity) hpx k
      rw [one_div, Real.rpow_inv_natCast_pow hx0.le (by omega)] at h1
      exact h1
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h2 : Real.log x / x * (p:ℝ) ^ k / k ≤ Real.log x / x * (p:ℝ) ^ k :=
      div_le_self (by positivity) hk1
    have h3 : Real.log x / x * (p:ℝ) ^ k ≤ Real.log x / x * x :=
      mul_le_mul_of_nonneg_left hpk (by positivity)
    have h4 : Real.log x / x * x = Real.log x := by field_simp
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (S.card : ℝ) ≤ x ^ (1/3:ℝ) := by
    have h1 : S.card ≤ ⌊x ^ ((1:ℝ) / k)⌋₊ :=
      (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ioc]; omega)
    have h2 : (⌊x ^ ((1:ℝ) / k)⌋₊ : ℝ) ≤ x ^ ((1:ℝ) / k) := Nat.floor_le (by positivity)
    have h3 : x ^ ((1:ℝ) / k) ≤ x ^ (1/3:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hx
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      have : (3:ℝ) ≤ k := by exact_mod_cast hk
      linarith
    exact (Nat.cast_le.mpr h1).trans (h2.trans h3)
  have : (S.card : ℝ) * -Real.log x ≥ -(x ^ (1/3:ℝ) * Real.log x) := by nlinarith
  rw [Tk]
  linarith

lemma sum_Tk_ge {x : ℝ} (hx : 1 ≤ x) :
    -(2 * (x ^ (1/3:ℝ) * Real.log x ^ 2)) ≤
      ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊, Tk x k := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsum := Finset.sum_le_sum (fun k (hk : k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊) =>
    Tk_ge hx (Finset.mem_Icc.mp hk).1)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : ((Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).card : ℝ) ≤ 2 * Real.log x := by
    have : (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).card ≤ ⌊Real.log x / Real.log 2⌋₊ := by
      rw [Nat.card_Icc]; omega
    exact (Nat.cast_le.mpr this).trans (floor_log_div_le hx)
  have hq : 0 ≤ x ^ (1/3:ℝ) * Real.log x := by positivity
  have : ((Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).card : ℝ) * -(x ^ (1/3:ℝ) * Real.log x) ≥
      -(2 * (x ^ (1/3:ℝ) * Real.log x ^ 2)) := by
    have e : 2 * (x ^ (1/3:ℝ) * Real.log x ^ 2) = 2 * Real.log x * (x ^ (1/3:ℝ) * Real.log x) := by
      ring
    rw [e]; nlinarith
  linarith

/-! ### The `j ≥ 3` part of `M(x)` -/

lemma incr_ge_half {p j : ℕ} (hp : 2 ≤ p) (hj : 3 ≤ j) : (p:ℝ) ^ 3 / 2 ≤ incr p j := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  unfold incr
  rw [if_neg (by omega)]
  have e : (p:ℝ) ^ j = p * (p:ℝ) ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : (p:ℝ) ^ 3 ≤ (p:ℝ) ^ j := pow_le_pow_right₀ (by linarith) hj
  have h0 : (0:ℝ) ≤ (p:ℝ) ^ (j - 1) := pow_nonneg (by linarith) _
  rw [e] at h1 ⊢
  nlinarith

lemma Delta_large_le {x : ℝ} (hx : 4 ≤ x) {p j : ℕ} (hp : p.Prime) (hpx : (p:ℝ) ≤ x)
    (hj : 3 ≤ j) :
    max 0 (Delta x p j) ≤ if (p:ℝ) < 2 * x ^ (1/3:ℝ) then Real.log x else 0 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hlpx : Real.log p ≤ Real.log x := Real.log_le_log (by linarith) hpx
  by_cases hD : Delta x p j ≤ 0
  · rw [max_eq_left hD]
    split_ifs <;> linarith
  · push Not at hD
    have hinc := incr_ge_half hp.two_le hj
    have hinc0 : 0 ≤ incr p j := le_trans (by positivity) hinc
    have hlam0 : 0 ≤ Real.log x / x := by positivity
    rw [Delta] at hD
    have h1 : Real.log x / x * ((p:ℝ) ^ 3 / 2) < Real.log x := by
      have := mul_le_mul_of_nonneg_left hinc hlam0
      linarith
    have h2 : (p:ℝ) ^ 3 < 2 * x := by
      have e : Real.log x / x * ((p:ℝ) ^ 3 / 2) = Real.log x * ((p:ℝ) ^ 3 / (2 * x)) := by
        field_simp
      rw [e] at h1
      have : (p:ℝ) ^ 3 / (2 * x) < 1 := by
        by_contra hc; push Not at hc; nlinarith
      rwa [div_lt_one (by positivity)] at this
    have h3 : (p:ℝ) < 2 * x ^ (1/3:ℝ) := by
      by_contra hc
      push Not at hc
      have hc3 : (2 * x ^ (1/3:ℝ)) ^ 3 ≤ (p:ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hc 3
      have e : (2 * x ^ (1/3:ℝ)) ^ 3 = 8 * x := by
        rw [mul_pow, show (1/3:ℝ) = ((3:ℕ):ℝ)⁻¹ by norm_num,
          Real.rpow_inv_natCast_pow hx0.le (by norm_num)]
        norm_num
      linarith
    rw [if_pos h3, Delta, max_eq_right hD.le]
    have : 0 ≤ Real.log x / x * incr p j := mul_nonneg hlam0 hinc0
    linarith

lemma J_le {x : ℝ} (hx : 4 ≤ x) : ((Nat.log 2 ⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hfl : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have h1 : 2 ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 hfl.ne'
  have h2 : ((2 ^ Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr h1).trans (Nat.floor_le hx0.le)
  have h3 : (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 ≤ Real.log x := by
    have := Real.log_le_log (by positivity) h2
    rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
  have h4 : (Nat.log 2 ⌊x⌋₊ : ℝ) ≤ 2 * Real.log x := by
    have h0 : (0:ℝ) ≤ Nat.log 2 ⌊x⌋₊ := Nat.cast_nonneg _
    nlinarith
  push_cast
  linarith

lemma V_le {x : ℝ} (hx : 4 ≤ x) :
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
        ∑ j ∈ Finset.Icc 3 (Nat.log 2 ⌊x⌋₊ + 1), max 0 (Delta x p j) ≤
      9 * (x ^ (1/3:ℝ) * Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ Real.log x := one_le_log_of_three_le (by linarith)
  set J := Nat.log 2 ⌊x⌋₊ + 1 with hJ
  set y := 2 * x ^ (1/3:ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hterm : ∀ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
      ∑ j ∈ Finset.Icc 3 J, max 0 (Delta x p j) ≤
        (J : ℝ) * (if (p:ℝ) < y then Real.log x else 0) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hpN : p < ⌊x⌋₊ + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have hpx : (p:ℝ) ≤ x := (Nat.cast_le.mpr (by omega : p ≤ ⌊x⌋₊)).trans (Nat.floor_le hx0.le)
    have h1 := Finset.sum_le_sum (fun j (hj : j ∈ Finset.Icc 3 J) =>
      Delta_large_le hx hpp hpx (Finset.mem_Icc.mp hj).1)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hc : ((Finset.Icc 3 J).card : ℝ) ≤ J := by
      exact_mod_cast (by rw [Nat.card_Icc]; omega : (Finset.Icc 3 J).card ≤ J)
    have hnn : (0:ℝ) ≤ (if (p:ℝ) < y then Real.log x else 0) := by split_ifs <;> linarith
    calc _ ≤ ((Finset.Icc 3 J).card : ℝ) * (if (p:ℝ) < y then Real.log x else 0) := h1
      _ ≤ (J : ℝ) * (if (p:ℝ) < y then Real.log x else 0) := mul_le_mul_of_nonneg_right hc hnn
  have hs1 := Finset.sum_le_sum hterm
  have hs2 : ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
      (J : ℝ) * (if (p:ℝ) < y then Real.log x else 0) ≤
      ∑ p ∈ Finset.range (⌊x⌋₊ + 1), (J : ℝ) * (if (p:ℝ) < y then Real.log x else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p _ _
    apply mul_nonneg (Nat.cast_nonneg _)
    split_ifs <;> linarith
  have hs3 : ∑ p ∈ Finset.range (⌊x⌋₊ + 1), (J : ℝ) * (if (p:ℝ) < y then Real.log x else 0) =
      (J : ℝ) * Real.log x * ((Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p:ℝ) < y)).card := by
    rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcard : (((Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p:ℝ) < y)).card : ℝ) ≤ y + 1 := by
    have h1 : (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p:ℝ) < y) ⊆ Finset.range ⌈y⌉₊ := by
      intro p hp
      rw [Finset.mem_range]
      exact Nat.lt_ceil.mpr (Finset.mem_filter.mp hp).2
    have h2 := Finset.card_le_card h1
    rw [Finset.card_range] at h2
    have h3 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
    have : (((Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p:ℝ) < y)).card : ℝ) ≤ ⌈y⌉₊ :=
      by exact_mod_cast h2
    linarith
  have hJ3 := J_le hx
  rw [← hJ] at hJ3
  have hx13 : 1 ≤ x ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hJ0 : (0:ℝ) ≤ J := Nat.cast_nonneg _
  have hfin : (J : ℝ) * Real.log x * (y + 1) ≤ 9 * (x ^ (1/3:ℝ) * Real.log x ^ 2) := by
    have a1 : y + 1 ≤ 3 * x ^ (1/3:ℝ) := by rw [hy]; linarith
    have a2 : (J : ℝ) * Real.log x ≤ 3 * Real.log x * Real.log x :=
      mul_le_mul_of_nonneg_right hJ3 (by linarith)
    have a3 : (J : ℝ) * Real.log x * (y + 1) ≤ 3 * Real.log x * Real.log x * (3 * x ^ (1/3:ℝ)) :=
      mul_le_mul a2 a1 (by linarith) (by positivity)
    nlinarith
  have hcard' : (J : ℝ) * Real.log x *
      (((Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p:ℝ) < y)).card : ℝ) ≤
      (J : ℝ) * Real.log x * (y + 1) :=
    mul_le_mul_of_nonneg_left hcard (by positivity)
  linarith

/-! ### Assembly: lower bound for `G = λ R_W(x) - M(x)` -/

lemma Delta_one_nonneg {x : ℝ} (hx : 4 ≤ x) {p : ℕ} (hp : p.Prime) (hpx : (p:ℝ) ≤ x) :
    0 ≤ Real.log p - Real.log x / x * p := by
  have hx0 : 0 < x := by linarith
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  rcases Nat.lt_or_ge p 3 with h | h
  · have hp2 : p = 2 := by have := hp.two_le; omega
    subst hp2
    have h1 := log_div_self_antitone exp_one_le_four hx
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h4] at h1
    push_cast
    have : Real.log x / x * 2 ≤ 2 * Real.log 2 / 4 * 2 := by linarith
    linarith
  · have h3 : (3:ℝ) ≤ p := by exact_mod_cast h
    have he : Real.exp 1 ≤ p := by have := Real.exp_one_lt_d9; linarith
    have h1 := log_div_self_antitone he hpx
    have : Real.log x / x * p ≤ Real.log p / p * p := mul_le_mul_of_nonneg_right h1 hp0.le
    rw [div_mul_cancel₀ _ hp0.ne'] at this
    linarith

lemma T1_eq_U1 {x : ℝ} (hx : 4 ≤ x) :
    Tk x 1 = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, max 0 (Delta x p 1) := by
  have hx0 : 0 < x := by linarith
  rw [Tk]
  simp only [Nat.cast_one, div_one, Real.rpow_one, pow_one]
  have hset : (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime = (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, h1⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨h1, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
  refine Finset.sum_congr hset (fun p hp => ?_)
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  have hpN : p < ⌊x⌋₊ + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  have hpx : (p:ℝ) ≤ x := (Nat.cast_le.mpr (by omega : p ≤ ⌊x⌋₊)).trans (Nat.floor_le hx0.le)
  have hincr : incr p 1 = p := by simp [incr]
  rw [Delta, hincr, max_eq_right (Delta_one_nonneg hx hpp hpx)]

lemma Tk_two_eq (x : ℝ) :
    Tk x 2 = ∑ p ∈ (Finset.Ioc 0 ⌊Real.sqrt x⌋₊).filter Nat.Prime,
      (Real.log p - Real.log x / x * (p:ℝ) ^ 2 / 2) := by
  have h : x ^ ((1:ℝ) / ((2:ℕ):ℝ)) = Real.sqrt x := by rw [Real.sqrt_eq_rpow]; norm_num
  rw [Tk, h]
  simp only [Nat.cast_ofNat]

lemma Mfun_split {x : ℝ} (hx : 4 ≤ x) :
    Mfun x = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, max 0 (Delta x p 1) +
      ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, max 0 (Delta x p 2) +
      ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
        ∑ j ∈ Finset.Icc 3 (Nat.log 2 ⌊x⌋₊ + 1), max 0 (Delta x p j) := by
  have hJ : 2 ≤ Nat.log 2 ⌊x⌋₊ + 1 := by
    have : 0 < Nat.log 2 ⌊x⌋₊ := Nat.log_pos (by norm_num) (Nat.le_floor (by push_cast; linarith))
    omega
  rw [Mfun, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact sum_Icc_one_split (fun j => max 0 (Delta x p j)) hJ

/-- **Lower bound for `G = λ R_W(x) - M(x)`** (under RH). -/
theorem G_lower (hψ : PsiBound) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 16 ≤ x →
    (2 - Real.sqrt 2) / 3 * Real.sqrt x - (5 + Real.log x + 8 / 3 * (Real.sqrt x / Real.log x) +
      C * (x ^ (1/3:ℝ) * Real.log x ^ 2)) ≤ Real.log x / x * RW x - Mfun x := by
  obtain ⟨C₁, hC₁, hθ⟩ := theta_error hψ
  refine ⟨2 * C₁ + 11, by linarith, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  rw [lam_RW_eq_sum_Tk hx1, sum_Icc_one_split _ (log_div_log_two_ge_two (by linarith)),
    Mfun_split (by linarith), ← T1_eq_U1 (by linarith)]
  have hT2 := T2_lower hC₁ hθ hx
  rw [← Tk_two_eq] at hT2
  have hU2 := M2_upper hC₁ hθ hx
  have hT3 := sum_Tk_ge hx1.le
  have hV := V_le (by linarith : (4:ℝ) ≤ x)
  have hq : x ^ (1/4:ℝ) * Real.log x ^ 2 ≤ x ^ (1/3:ℝ) * Real.log x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hq1 : C₁ * (x ^ (1/4:ℝ) * Real.log x ^ 2) ≤ C₁ * (x ^ (1/3:ℝ) * Real.log x ^ 2) :=
    mul_le_mul_of_nonneg_left hq hC₁
  have e : (2 - Real.sqrt 2) / 3 * Real.sqrt x = 2 / 3 * Real.sqrt x - Real.sqrt 2 / 3 * Real.sqrt x := by
    ring
  rw [e]
  linarith

end LandauRH

end

-- ===== LF7Final.lean =====
section

set_option autoImplicit false

open Set Filter Topology Asymptotics

namespace LandauRH

open LandauFunction

/-! ### Asymptotics of the error terms -/

lemma isLittleO_const_sqrt (A : ℝ) : (fun _ : ℝ => A) =o[atTop] (fun x => Real.sqrt x) := by
  rw [isLittleO_const_left]
  right
  exact tendsto_norm_atTop_atTop.comp Real.tendsto_sqrt_atTop

lemma isLittleO_log_sqrt : (fun x : ℝ => Real.log x) =o[atTop] (fun x => Real.sqrt x) := by
  have h := isLittleO_log_rpow_rpow_atTop (s := 1/2) 1 (by norm_num)
  refine h.congr' (Eventually.of_forall (fun x => ?_)) (Eventually.of_forall (fun x => ?_))
  · simp only [Real.rpow_one]
  · simp only [Real.sqrt_eq_rpow]

lemma isLittleO_sqrt_div_log :
    (fun x : ℝ => Real.sqrt x / Real.log x) =o[atTop] (fun x => Real.sqrt x) := by
  have h1 : (fun x : ℝ => (Real.log x)⁻¹) =o[atTop] (fun _ => (1:ℝ)) := by
    rw [isLittleO_one_iff]
    exact tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h2 : (fun x : ℝ => Real.sqrt x) =O[atTop] (fun x => Real.sqrt x) := isBigO_refl _ _
  have h := h2.mul_isLittleO h1
  refine h.congr' (Eventually.of_forall (fun x => ?_)) (Eventually.of_forall (fun x => ?_))
  · simp only [div_eq_mul_inv]
  · simp only [mul_one]

lemma isLittleO_rpow_log :
    (fun x : ℝ => x ^ (1/3:ℝ) * Real.log x ^ 2) =o[atTop] (fun x => Real.sqrt x) := by
  have h1 := isLittleO_log_rpow_rpow_atTop (s := 1/6) 2 (by norm_num)
  have h2 : (fun x : ℝ => x ^ (1/3:ℝ)) =O[atTop] (fun x => x ^ (1/3:ℝ)) := isBigO_refl _ _
  have h := h2.mul_isLittleO h1
  refine h.congr' (Eventually.of_forall (fun x => ?_)) ?_
  · beta_reduce
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  · filter_upwards [eventually_gt_atTop 0] with x hx
    beta_reduce
    rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]
    norm_num

lemma eventually_error_lt (A B D ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, A + Real.log x + B * (Real.sqrt x / Real.log x) +
      D * (x ^ (1/3:ℝ) * Real.log x ^ 2) < ε * Real.sqrt x := by
  have h := (((isLittleO_const_sqrt A).add isLittleO_log_sqrt).add
    (isLittleO_sqrt_div_log.const_mul_left B)).add (isLittleO_rpow_log.const_mul_left D)
  have h2 := h.def (half_pos hε)
  filter_upwards [h2, eventually_gt_atTop 0] with x hx hx0
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs] at hx
  have := le_abs_self (A + Real.log x + B * (Real.sqrt x / Real.log x) +
    D * (x ^ (1/3:ℝ) * Real.log x ^ 2))
  nlinarith

/-! ### The main inequality and the RH ⇒ direction -/

/-- Given the `ψ₁` and `ψ` bounds, `λ Li(x²) + M(x) < x` for all large `x`. -/
theorem main_ineq (hP : Psi1Bound) (hψ : PsiBound) :
    ∀ᶠ x : ℝ in atTop, Real.log x / x * logIntegral (x ^ 2) + Mfun x < x := by
  obtain ⟨K, C, hK, hC, hQ⟩ := Q_lower hP
  obtain ⟨C', hC', hG⟩ := G_lower hψ
  have hE := eventually_error_lt (K + 5) (8 * |Sstar| + 8 / 3) (C + C') (1 / 200) (by norm_num)
  filter_upwards [hE, eventually_ge_atTop 16] with x hE hx
  have hq := hQ x (by linarith)
  have hg := hG x hx
  have hS := Sstar_lt
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≠ 0 := log_ne_zero_of_one_lt (by linarith)
  have hid : Real.log x / x * (x ^ 2 / Real.log x) = x := by field_simp
  have hq4 : x ^ (1/4:ℝ) * Real.log x ^ 2 ≤ x ^ (1/3:ℝ) * Real.log x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hq4' : C * (x ^ (1/4:ℝ) * Real.log x ^ 2) ≤ C * (x ^ (1/3:ℝ) * Real.log x ^ 2) :=
    mul_le_mul_of_nonneg_left hq4 hC
  have hpos : 0 < ((2 - Real.sqrt 2) / 3 - 1 / 200 - Sstar) * Real.sqrt x :=
    mul_pos (by linarith) (Real.sqrt_pos.mpr hx0)
  set lam := Real.log x / x with hlam
  set Li := logIntegral (x ^ 2) with hLi
  set R := RW x with hR
  have key : x - (lam * Li + Mfun x) = lam * (x ^ 2 / Real.log x - Li - R) + (lam * R - Mfun x) := by
    linear_combination (-1:ℝ) * hid
  have e1 : (8 * |Sstar| + 8 / 3) * (Real.sqrt x / Real.log x) =
      8 * |Sstar| * (Real.sqrt x / Real.log x) + 8 / 3 * (Real.sqrt x / Real.log x) := by ring
  have e2 : (C + C') * (x ^ (1/3:ℝ) * Real.log x ^ 2) =
      C * (x ^ (1/3:ℝ) * Real.log x ^ 2) + C' * (x ^ (1/3:ℝ) * Real.log x ^ 2) := by ring
  rw [e1, e2] at hE
  have e3 : ((2 - Real.sqrt 2) / 3 - 1 / 200 - Sstar) * Real.sqrt x =
      (2 - Real.sqrt 2) / 3 * Real.sqrt x - 1 / 200 * Real.sqrt x - Sstar * Real.sqrt x := by ring
  rw [e3] at hpos
  have e4 : -Sstar * Real.sqrt x = -(Sstar * Real.sqrt x) := by ring
  rw [e4] at hq
  linarith

/-- **The Landau inequality holds for all large `n`**, given the `ψ₁` and `ψ` bounds. -/
theorem landau_of_bounds (hP : Psi1Bound) (hψ : PsiBound) :
    ∀ᶠ n : ℕ in atTop, Real.log (landau n) < Real.sqrt (logIntegralInv n) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((main_ineq hP hψ).and (eventually_ge_atTop 16))
  rw [eventually_atTop]
  refine ⟨⌈X ^ 2 / Real.log 2⌉₊, fun n hn => ?_⟩
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨hLi, hy2⟩ := logIntegral_logIntegralInv hn0
  have hy := logIntegralInv_ge hn0
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnX : X ^ 2 / Real.log 2 ≤ n := Nat.ceil_le.mp hn
  have hX2 : X ^ 2 ≤ n * Real.log 2 := by rwa [div_le_iff₀ hl2] at hnX
  set y := logIntegralInv (n:ℝ) with hydef
  have hxX : X ≤ Real.sqrt y := (le_abs_self X).trans (Real.abs_le_sqrt (by linarith))
  obtain ⟨hineq, hx16⟩ := hX (Real.sqrt y) hxX
  have hland := log_landau_le n (by linarith : (4:ℝ) ≤ Real.sqrt y)
  have hxx : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  rw [hxx, hLi] at hineq
  linarith


/-- Variant of `main_ineq` with an additive slack `2` inside `Li`. -/
theorem main_ineq2 (hP : Psi1Bound) (hψ : PsiBound) :
    ∀ᶠ x : ℝ in atTop, Real.log x / x * (logIntegral (x ^ 2) + 2) + Mfun x < x := by
  obtain ⟨K, C, hK, hC, hQ⟩ := Q_lower hP
  obtain ⟨C', hC', hG⟩ := G_lower hψ
  have hE := eventually_error_lt (K + 5) (8 * |Sstar| + 8 / 3) (C + C') (1 / 200) (by norm_num)
  have hS := Sstar_lt
  have hm : 0 < (2 - Real.sqrt 2) / 3 - 1 / 200 - Sstar := by linarith
  have hbig : ∀ᶠ x : ℝ in atTop, 2 < ((2 - Real.sqrt 2) / 3 - 1 / 200 - Sstar) * Real.sqrt x :=
    (Filter.Tendsto.const_mul_atTop hm Real.tendsto_sqrt_atTop).eventually_gt_atTop 2
  filter_upwards [hE, eventually_ge_atTop 16, hbig] with x hE hx hbig
  have hq := hQ x (by linarith)
  have hg := hG x hx
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≠ 0 := log_ne_zero_of_one_lt (by linarith)
  have hid : Real.log x / x * (x ^ 2 / Real.log x) = x := by field_simp
  have hq4 : x ^ (1/4:ℝ) * Real.log x ^ 2 ≤ x ^ (1/3:ℝ) * Real.log x ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hq4' : C * (x ^ (1/4:ℝ) * Real.log x ^ 2) ≤ C * (x ^ (1/3:ℝ) * Real.log x ^ 2) :=
    mul_le_mul_of_nonneg_left hq4 hC
  have hlam1 : Real.log x / x ≤ 1 := lam_le_one hx0
  have hpos : 2 * (Real.log x / x) < ((2 - Real.sqrt 2) / 3 - 1 / 200 - Sstar) * Real.sqrt x := by
    linarith
  set lam := Real.log x / x with hlam
  set Li := logIntegral (x ^ 2) with hLi
  set R := RW x with hR
  have key : x - (lam * (Li + 2) + Mfun x) =
      lam * (x ^ 2 / Real.log x - Li - R) + (lam * R - Mfun x) - 2 * lam := by
    linear_combination (-1:ℝ) * hid
  have e1 : (8 * |Sstar| + 8 / 3) * (Real.sqrt x / Real.log x) =
      8 * |Sstar| * (Real.sqrt x / Real.log x) + 8 / 3 * (Real.sqrt x / Real.log x) := by ring
  have e2 : (C + C') * (x ^ (1/3:ℝ) * Real.log x ^ 2) =
      C * (x ^ (1/3:ℝ) * Real.log x ^ 2) + C' * (x ^ (1/3:ℝ) * Real.log x ^ 2) := by ring
  rw [e1, e2] at hE
  have e3 : ((2 - Real.sqrt 2) / 3 - 1 / 200 - Sstar) * Real.sqrt x =
      (2 - Real.sqrt 2) / 3 * Real.sqrt x - 1 / 200 * Real.sqrt x - Sstar * Real.sqrt x := by ring
  rw [e3] at hpos
  have e4 : -Sstar * Real.sqrt x = -(Sstar * Real.sqrt x) := by ring
  rw [e4] at hq
  linarith

/-- The Landau inequality with the shifted inverse `Li⁻¹(n - 2)`. -/
theorem landau_of_bounds2 (hP : Psi1Bound) (hψ : PsiBound) :
    ∀ᶠ n : ℕ in atTop, Real.log (landau n) < Real.sqrt (logIntegralInv ((n:ℝ) - 2)) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((main_ineq2 hP hψ).and (eventually_ge_atTop 16))
  rw [eventually_atTop]
  refine ⟨⌈X ^ 2 / Real.log 2⌉₊ + 2, fun n hn => ?_⟩
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast (le_trans (Nat.le_add_left 2 _) hn)
  have hn0 : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  obtain ⟨hLi, hy2⟩ := logIntegral_logIntegralInv hn0
  have hy := logIntegralInv_ge hn0
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnX : X ^ 2 / Real.log 2 ≤ (n:ℝ) - 2 := by
    have hc : ((⌈X ^ 2 / Real.log 2⌉₊ + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at hc
    linarith [Nat.le_ceil (X ^ 2 / Real.log 2)]
  have hX2 : X ^ 2 ≤ ((n:ℝ) - 2) * Real.log 2 := by rwa [div_le_iff₀ hl2] at hnX
  set y := logIntegralInv ((n:ℝ) - 2) with hydef
  have hxX : X ≤ Real.sqrt y := (le_abs_self X).trans (Real.abs_le_sqrt (by linarith))
  obtain ⟨hineq, hx16⟩ := hX (Real.sqrt y) hxX
  have hland := log_landau_le n (by linarith : (4:ℝ) ≤ Real.sqrt y)
  have hxx : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  rw [hxx, hLi] at hineq
  have e : Real.log (Real.sqrt y) / Real.sqrt y * ((n:ℝ) - 2 + 2) =
      Real.log (Real.sqrt y) / Real.sqrt y * n := by ring
  linarith

/-! ### The principal-value logarithmic integral -/

/-- Ramanujan's series for the principal value `li`. -/
noncomputable def liPV (y : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log |Real.log y| +
    ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))

noncomputable def serS (u : ℝ) : ℝ :=
  ∑' k : ℕ, u^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))

lemma summable_pow_div_succ_factorial (u : ℝ) :
    Summable (fun k : ℕ => |u| ^ k / ((k+1).factorial : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (Real.summable_pow_div_factorial |u|)
  have hf : (k.factorial : ℝ) ≤ ((k+1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf

lemma hasDerivAt_serS (u : ℝ) :
    HasDerivAt serS (∑' k : ℕ, u ^ k / ((k+1).factorial : ℝ)) u := by
  set R := |u| + 1 with hRdef
  have hR : 0 < R := by positivity
  unfold serS
  refine hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-R) R) (y₀ := 0)
    (u := fun k : ℕ => |R| ^ k / ((k+1).factorial : ℝ))
    (g' := fun k (z : ℝ) => z ^ k / ((k+1).factorial : ℝ))
    (summable_pow_div_succ_factorial R) isOpen_Ioo isPreconnected_Ioo ?_ ?_ ?_ ?_ ?_
  · intro k z _
    have := (hasDerivAt_pow (k+1) z).div_const ((((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)))
    have h1 : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
    refine this.congr_deriv ?_
    rw [Nat.add_sub_cancel, mul_div_mul_left _ _ h1]
  · intro k z hz
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0:ℝ) < ((k+1).factorial : ℝ))]
    have hzR : |z| ≤ |R| := by
      rw [abs_of_pos hR, abs_le]; constructor <;> linarith [hz.1, hz.2]
    gcongr
  · simp only [Set.mem_Ioo]; constructor <;> linarith
  · simp
  · simp only [Set.mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]

lemma mul_tsum_exp_aux (u : ℝ) :
    u * ∑' k : ℕ, u ^ k / ((k+1).factorial : ℝ) = Real.exp u - 1 := by
  have hs : Summable (fun k : ℕ => u ^ k / (k.factorial : ℝ)) := Real.summable_pow_div_factorial u
  have hexp : Real.exp u = ∑' k : ℕ, u ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, add_sub_cancel_left]
  congr 1
  funext k
  rw [pow_succ]
  ring

lemma hasDerivAt_liPV {y : ℝ} (hy : 1 < y) : HasDerivAt liPV (1 / Real.log y) y := by
  have hl : 0 < Real.log y := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  have h2 : HasDerivAt (fun z => Real.log (Real.log z)) ((Real.log y)⁻¹ * y⁻¹) y :=
    (Real.hasDerivAt_log hl.ne').comp y (Real.hasDerivAt_log hy0.ne')
  have h3 : HasDerivAt (fun z => serS (Real.log z))
      ((∑' k : ℕ, (Real.log y) ^ k / ((k+1).factorial : ℝ)) * y⁻¹) y :=
    (hasDerivAt_serS _).comp y (Real.hasDerivAt_log hy0.ne')
  have hfun : liPV = fun z => Real.eulerMascheroniConstant + Real.log (Real.log z) + serS (Real.log z) := by
    funext z; simp [liPV, serS, Real.log_abs]
  rw [hfun]
  refine ((h2.const_add Real.eulerMascheroniConstant).add h3).congr_deriv ?_
  have hT := mul_tsum_exp_aux (Real.log y)
  rw [Real.exp_log hy0] at hT
  set T := ∑' k : ℕ, (Real.log y) ^ k / ((k+1).factorial : ℝ)
  have hT' : T = (y - 1) / Real.log y := by
    field_simp; linarith
  rw [hT']
  field_simp
  ring

lemma liPV_eq {y : ℝ} (hy : 2 ≤ y) : liPV y = logIntegral y + liPV 2 := by
  unfold logIntegral
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := liPV)
    (fun x hx => hasDerivAt_liPV (by rw [Set.uIcc_of_le hy] at hx; linarith [hx.1]))
    (intervalIntegrable_one_div_log (by norm_num) (by linarith))]
  ring

lemma serS_log_two_bounds : 0 ≤ serS (Real.log 2) ∧ serS (Real.log 2) ≤ 1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set u := Real.log 2
  have hs : Summable (fun k : ℕ => u ^ k / ((k+1).factorial : ℝ)) := by
    have := summable_pow_div_succ_factorial u
    rwa [abs_of_pos hl] at this
  have hs' : Summable (fun k : ℕ => u * (u ^ k / ((k+1).factorial : ℝ))) := hs.mul_left u
  have hle : ∀ k : ℕ, u^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) ≤
      u * (u ^ k / ((k+1).factorial : ℝ)) := by
    intro k
    rw [pow_succ, mul_div_assoc', mul_comm (u ^ k) u]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (1:ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    nlinarith [(by positivity : (0:ℝ) < ((k+1).factorial : ℝ))]
  have h0 : ∀ k : ℕ, 0 ≤ u^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)) := fun k => by positivity
  have hsS : Summable (fun k : ℕ => u^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))) :=
    Summable.of_nonneg_of_le h0 hle hs'
  refine ⟨tsum_nonneg h0, ?_⟩
  unfold serS
  calc ∑' k : ℕ, u^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
      ≤ ∑' k : ℕ, u * (u ^ k / ((k+1).factorial : ℝ)) := hsS.tsum_le_tsum hle hs'
    _ = u * ∑' k : ℕ, u ^ k / ((k+1).factorial : ℝ) := tsum_mul_left
    _ = 1 := by rw [mul_tsum_exp_aux, Real.exp_log (by norm_num)]; norm_num

lemma liPV_two_bounds : -1 ≤ liPV 2 ∧ liPV 2 ≤ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl0 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  obtain ⟨hS0, hS1⟩ := serS_log_two_bounds
  have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ0 := Real.one_half_lt_eulerMascheroniConstant
  have hll : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hl.le hl1.le
  have hll' : 1 - (Real.log 2)⁻¹ ≤ Real.log (Real.log 2) := Real.one_sub_inv_le_log_of_pos hl
  have hinv : (Real.log 2)⁻¹ ≤ 1.5 := by
    rw [inv_le_comm₀ hl (by norm_num)]; linarith
  have e : liPV 2 = Real.eulerMascheroniConstant + Real.log (Real.log 2) + serS (Real.log 2) := by
    simp [liPV, serS, Real.log_abs]
  rw [e]
  constructor <;> linarith

end LandauRH

end


end

theorem solution :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let inv (y : ℝ) := sInf {x : ℝ | 2 ≤ x ∧ y ≤ li x}
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (LandauFunction.landau n) < Real.sqrt (inv n) := by
  intro li inv
  have hli : ∀ y, li y = LandauRH.liPV y := fun y => rfl
  filter_upwards [LandauRH.landau_of_bounds2
    (LandauCriterion.psi1_error_of_riemannHypothesis riemann_hypothesis)
    (LandauCriterion.psi_error_of_riemannHypothesis riemann_hypothesis)] with n hn
  refine lt_of_lt_of_le hn (Real.sqrt_le_sqrt ?_)
  obtain ⟨h2m, h2p⟩ := LandauRH.liPV_two_bounds
  show sInf {x : ℝ | 2 ≤ x ∧ (n:ℝ) - 2 ≤ LandauFunction.logIntegral x} ≤
    sInf {x : ℝ | 2 ≤ x ∧ (n:ℝ) ≤ li x}
  apply csInf_le_csInf ⟨2, fun x hx => hx.1⟩
  · set m : ℝ := (n:ℝ) + 1
    have hm : 0 ≤ m := by positivity
    set x₁ : ℝ := (4 * m + 8) ^ 2 with hx₁
    have hx₁64 : 64 ≤ x₁ := by rw [hx₁]; nlinarith
    have hsq : Real.sqrt x₁ = 4 * m + 8 := by rw [hx₁]; exact Real.sqrt_sq (by linarith)
    refine ⟨x₁, by linarith, ?_⟩
    have h1 := LandauRH.logIntegral_ge (y := x₁) (by linarith)
    have h2 := LandauRH.log_le_two_sqrt (x := x₁) (by linarith)
    rw [hsq] at h2
    have hlog : 0 < Real.log x₁ := Real.log_pos (by linarith)
    have h3 : m ≤ (x₁ - 2) / Real.log x₁ := by
      rw [le_div_iff₀ hlog]
      nlinarith
    rw [hli, LandauRH.liPV_eq (by linarith)]
    linarith
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have := hx.2
    rw [hli, LandauRH.liPV_eq hx.1] at this
    linarith
