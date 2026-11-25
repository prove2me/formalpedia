-- Prove2me | solution 1 for DeficitPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:40:36.493322+00:00
-- url     : https://prove2.me/submissions/c8910886-c906-4708-9579-18d2074ff6a5

module
public import Definitions.Def_PHarmonicPoly_LagrangeDerivCoeffOne
public import Definitions.Def_PHarmonicPoly_LagrangeDerivSigns
public import Definitions.Def_PHarmonicPoly_DeficitPoly
public import Theorems.Thm_LagrangeDerivCoeffOne
public import Theorems.Thm_LagrangeDerivSigns


set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) {P : Polynomial ℝ}
    (hdeg : P.degree ≤ (m : ℕ))
    (hbd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) (h1 : P.eval 1 = 1) :
    2 * (1 + P.eval (Polynomial.Chebyshev.node m 1))
      ≤ ((m : ℝ) ^ 2 - (Polynomial.derivative P).eval 1)
          * (1 - Polynomial.Chebyshev.node m 1) := by
  classical
  set s : Finset ℕ := Finset.range (m + 1) with hs
  have hcard : s.card = m + 1 := by rw [hs, Finset.card_range]
  have hinj : Set.InjOn (Polynomial.Chebyshev.node m) ↑s :=
    (Polynomial.Chebyshev.strictAntiOn_node m).injOn
  have hk : 1 < s.card := by omega
  -- the coefficient family c i
  set c : ℕ → ℝ := fun i =>
    (∏ j ∈ s.erase i, (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j))⁻¹ *
      ∑ t ∈ Finset.powersetCard (m - 1) (s.erase i),
        ∏ a ∈ t, (1 - Polynomial.Chebyshev.node m a) with hc
  have hcardsub : s.card - (1 + 1) = m - 1 := by omega
  -- Step 1/2: the interpolation formula for a general Q of degree < #s
  have interp : ∀ Q : Polynomial ℝ, Q.degree < (s.card : ℕ) →
      (Polynomial.derivative Q).eval 1 = ∑ i ∈ s, Q.eval (Polynomial.Chebyshev.node m i) * c i := by
    intro Q hQ
    have key := Lagrange.eval_iterate_derivative_eq_sum hinj hQ hk (1 : ℝ)
    rw [Function.iterate_one] at key
    rw [key, hcardsub, hc]
    rw [Nat.factorial_one, Nat.cast_one, one_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_eq_mul_inv]
    ring
  -- apply to P
  have hPdeg : P.degree < (s.card : ℕ) := by
    rw [hcard]; exact lt_of_le_of_lt hdeg (by exact_mod_cast Nat.lt_succ_self m)
  have hP := interp P hPdeg
  -- apply to T_m
  have hTdeg : (Polynomial.Chebyshev.T ℝ (m : ℤ)).degree < (s.card : ℕ) := by
    rw [hcard, Polynomial.Chebyshev.degree_T, Int.natAbs_natCast]
    exact_mod_cast Nat.lt_succ_self m
  have hT := interp (Polynomial.Chebyshev.T ℝ (m : ℤ)) hTdeg
  have hTone : (Polynomial.derivative (Polynomial.Chebyshev.T ℝ (m : ℤ))).eval 1 = (m : ℝ) ^ 2 := by
    rw [Polynomial.Chebyshev.derivative_T_eval_one]; push_cast; ring
  have hTnode : ∀ i ∈ s, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval
      (Polynomial.Chebyshev.node m i) = (-1 : ℝ) ^ i := by
    intro i hi
    rw [hs, Finset.mem_range] at hi
    exact Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr (by omega))
  -- Step 2: subtract
  have hdiff : (m : ℝ) ^ 2 - (Polynomial.derivative P).eval 1
      = ∑ i ∈ s, ((-1 : ℝ) ^ i - P.eval (Polynomial.Chebyshev.node m i)) * c i := by
    rw [← hTone, hT, hP, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hTnode i hi]
    ring
  -- Step 3: every summand is nonnegative
  have hnonneg : ∀ i ∈ s,
      0 ≤ ((-1 : ℝ) ^ i - P.eval (Polynomial.Chebyshev.node m i)) * c i := by
    intro i hi
    rw [hs, Finset.mem_range] at hi
    have hsign : 0 ≤ (-1 : ℝ) ^ i * c i := by
      rw [hc, hs]
      exact LagrangeDerivSigns m i (by omega) (m - 1)
    have habs : |P.eval (Polynomial.Chebyshev.node m i)| ≤ 1 :=
      hbd _ Polynomial.Chebyshev.node_mem_Icc
    have hle : (-1 : ℝ) ^ i * P.eval (Polynomial.Chebyshev.node m i) ≤ 1 := by
      refine le_of_abs_le ?_
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact habs
    have hfac : ((-1 : ℝ) ^ i - P.eval (Polynomial.Chebyshev.node m i)) * c i
        = (1 - (-1 : ℝ) ^ i * P.eval (Polynomial.Chebyshev.node m i)) * ((-1 : ℝ) ^ i * c i) := by
      have hsq : ((-1 : ℝ) ^ i) * ((-1 : ℝ) ^ i) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      linear_combination (P.eval (Polynomial.Chebyshev.node m i) * c i) * hsq
    rw [hfac]
    exact mul_nonneg (by linarith) hsign
  -- Step 5: drop all summands but i = 1
  have hmem1 : (1 : ℕ) ∈ s := by rw [hs, Finset.mem_range]; omega
  have hsingle := Finset.single_le_sum hnonneg hmem1
  -- c 1 = -2/(1 - x_1)
  have hc1 : c 1 = -2 / (1 - Polynomial.Chebyshev.node m 1) := by
    rw [hc, hs]; exact LagrangeDerivCoeffOne hm
  -- Step 6: 1 - x_1 > 0
  have hx1 : Polynomial.Chebyshev.node m 1 < 1 := by
    have := Polynomial.Chebyshev.node_lt (n := m) (i := 0) (j := 1) (by omega) (by omega)
    rwa [Polynomial.Chebyshev.node_eq_one] at this
  have hpos : 0 < 1 - Polynomial.Chebyshev.node m 1 := by linarith
  rw [hdiff]
  rw [hc1] at hsingle
  have hterm : ((-1 : ℝ) ^ (1 : ℕ) - P.eval (Polynomial.Chebyshev.node m 1))
      * (-2 / (1 - Polynomial.Chebyshev.node m 1))
      = 2 * (1 + P.eval (Polynomial.Chebyshev.node m 1)) / (1 - Polynomial.Chebyshev.node m 1) := by
    rw [pow_one]
    field_simp
    ring
  rw [hterm, div_le_iff₀ hpos] at hsingle
  linarith [hsingle]
