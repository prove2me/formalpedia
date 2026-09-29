-- Prove2me | solution 2 for FourExp.small_irreducible_factor
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T08:02:51.821208+00:00
-- url     : https://prove2.me/submissions/5b3d2c39-4b53-44bd-a063-ec2ce406ce94

import Mathlib
import Theorems.Thm_Transcendence_exists_irreducible_factor_cofactor_bound

/-!
# A small irreducible factor (Gel'fond's lemma)

Let `P ∈ ℤ[X]` be primitive, with coefficients at most `H` and degree `d ≤ n ≤ log H`, and
`|P(α)| < H^(-λ n)`. A primitive constant is `±1`, whose value `1` is not small, so `d > 0`. The
multiplicative step of Gel'fond's lemma writes `P = Q^e R` with `Q` irreducible of positive degree
`δ` and `1 ≤ 2^(δ r) M(Q)^r M(R)^δ |R(α)|`, where `r = deg R` and `M` is the Mahler measure.

Put `L = log H`, `a = log M(Q) ≥ 0` and `b = log M(R) ≥ 0`. From
`M(Q)^e M(R) = M(P) ≤ √(d+1) H ≤ exp(d) H` we get `e a + b ≤ d + L`, so `a, b ≤ d + L ≤ 2L`. As
`δ, r ≤ d ≤ n ≤ L`, the logarithm of `2^(δ r) M(Q)^r M(R)^δ` is at most `nL + 2nL + 2nL`, and
`e log |Q(α)| < -λ n L - log |R(α)| ≤ -(λ - 5) n L`. For the coefficients,
`|Q_i| ≤ C(δ, i) M(Q) ≤ 2^δ M(Q)` and `e (δ log 2 + a) ≤ e δ + d + L ≤ 2n + L`. Finally
`e δ ≤ d ≤ n`. The multiplicity `e` is the `s` of the statement.
-/

open Polynomial

theorem solution
    (α : ℂ) (hα : Transcendental ℚ α) (P : Polynomial ℤ) (hprim : P.IsPrimitive)
    (H n lam : ℝ) (hPH : ∀ i : ℕ, |(P.coeff i : ℝ)| ≤ H)
    (hlog : n ≤ Real.log H) (hdeg : (P.natDegree : ℝ) ≤ n) (hlam : 6 < lam)
    (hsmall : ‖Polynomial.aeval α P‖ < H ^ (-(lam * n))) :
    ∃ Q : Polynomial ℤ, Q ∣ P ∧ Q.IsPrimitive ∧ Irreducible Q ∧
      ∃ s : ℕ, 0 < s ∧
        ‖Polynomial.aeval α Q‖ < H ^ (-((lam - 6) * n / s)) ∧
        (∀ i : ℕ, |(Q.coeff i : ℝ)| ≤ H ^ ((1 : ℝ) / s) * Real.exp (2 * n / s)) ∧
        (Q.natDegree : ℝ) ≤ n / s := by
  classical
  have hP0 : P ≠ 0 := hprim.ne_zero
  have hH1 : 1 ≤ H := le_trans (by exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hP0))
    (hPH P.natDegree)
  have hH0 : 0 < H := by linarith
  have hn0 : 0 ≤ n := (Nat.cast_nonneg _).trans hdeg
  have hL0 : 0 ≤ Real.log H := Real.log_nonneg hH1
  -- `P` is not constant
  have hdpos : 0 < P.natDegree := by
    by_contra h0
    have hPC := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h0)
    have hu : IsUnit (P.coeff 0) := hprim _ ⟨1, by rw [mul_one]; exact hPC⟩
    have h1 : ‖Polynomial.aeval α P‖ = 1 := by
      rw [hPC, aeval_C, algebraMap_int_eq, eq_intCast, Complex.norm_intCast]
      rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
    have h2 : H ^ (-(lam * n)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hH1 (by nlinarith)
    linarith
  obtain ⟨Q, R, e, hQirr, hQpos, he, hPeq, hgood⟩ :=
    Transcendence.exists_irreducible_factor_cofactor_bound P hdpos α
  have hR0 : R ≠ 0 := by rintro rfl; exact hP0 (by rw [hPeq, mul_zero])
  have hdeg_eq : (P.natDegree : ℝ) = e * Q.natDegree + R.natDegree := by
    rw [hPeq, natDegree_mul (pow_ne_zero _ hQirr.ne_zero) hR0, natDegree_pow]; push_cast; ring
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  -- Mahler measures: `M(Q)^e M(R) = M(P) ≤ √(d+1) H ≤ exp(d) H`
  set MQ := (Q.map (Int.castRingHom ℂ)).mahlerMeasure with hMQ
  set MR := (R.map (Int.castRingHom ℂ)).mahlerMeasure with hMR
  have hMQ1 : 1 ≤ MQ := one_le_mahlerMeasure_of_ne_zero hQirr.ne_zero
  have hMR1 : 1 ≤ MR := one_le_mahlerMeasure_of_ne_zero hR0
  have hB : MQ ^ e * MR ≤ Real.exp P.natDegree * H := by
    have heq : (P.map (Int.castRingHom ℂ)).mahlerMeasure = MQ ^ e * MR := by
      rw [hPeq, Polynomial.map_mul, Polynomial.map_pow, mahlerMeasure_mul, ← Multiset.prod_replicate,
        prod_mahlerMeasure_eq_mahlerMeasure_prod, Multiset.map_replicate, Multiset.prod_replicate]
    have hsup : (P.map (Int.castRingHom ℂ)).supNorm ≤ H := by
      obtain ⟨j, hj⟩ := (P.map (Int.castRingHom ℂ)).exists_eq_supNorm
      rw [hj, coeff_map, eq_intCast, Complex.norm_intCast]
      exact hPH j
    have hsq : √((P.natDegree : ℝ) + 1) ≤ Real.exp P.natDegree := by
      rw [Real.sqrt_le_left (Real.exp_pos _).le, sq, ← Real.exp_add]
      linarith [Real.add_one_le_exp (P.natDegree : ℝ), Real.exp_le_exp.2
        (by linarith : (P.natDegree : ℝ) ≤ P.natDegree + P.natDegree)]
    have hM := mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm (P.map (Int.castRingHom ℂ))
    rw [natDegree_map_eq_of_injective Int.cast_injective, heq] at hM
    exact hM.trans (mul_le_mul hsq hsup (supNorm_nonneg _) (Real.exp_pos _).le)
  -- the same bounds in logarithmic form
  have ha : 0 ≤ Real.log MQ := Real.log_nonneg hMQ1
  have hb : 0 ≤ Real.log MR := Real.log_nonneg hMR1
  have hab : e * Real.log MQ + Real.log MR ≤ P.natDegree + Real.log H := by
    have h := Real.log_le_log (by positivity) hB
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (Real.exp_pos _).ne' hH0.ne', Real.log_exp] at h
  have hvR : 0 < ‖aeval α R‖ := by
    rcases (norm_nonneg (aeval α R)).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hgood; linarith
    · exact h0
  have hgood' : 0 ≤ (Q.natDegree * R.natDegree : ℝ) * Real.log 2 + R.natDegree * Real.log MQ +
      Q.natDegree * Real.log MR + Real.log ‖aeval α R‖ := by
    have h := Real.log_le_log one_pos hgood
    rwa [Real.log_one, Real.log_mul (by positivity) hvR.ne', Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow, Nat.cast_mul] at h
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hδd : (e * Q.natDegree : ℝ) ≤ P.natDegree := by
    rw [hdeg_eq]; linarith [R.natDegree.cast_nonneg (α := ℝ)]
  have hδ : (Q.natDegree : ℝ) ≤ P.natDegree :=
    (le_mul_of_one_le_left (Nat.cast_nonneg _) he1).trans hδd
  have hr : (R.natDegree : ℝ) ≤ P.natDegree := by
    rw [hdeg_eq]; nlinarith [(Q.natDegree).cast_nonneg (α := ℝ)]
  have ha' : Real.log MQ ≤ P.natDegree + Real.log H := by
    linarith [le_mul_of_one_le_left ha he1]
  have hb' : Real.log MR ≤ P.natDegree + Real.log H := by nlinarith
  refine ⟨Q, ⟨Q ^ (e - 1) * R, by rw [hPeq, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]⟩,
    hQirr.isPrimitive hQpos.ne', hQirr, e, he, ?_, fun i => ?_, ?_⟩
  · -- the value at `α`
    rw [Real.rpow_def_of_pos hH0]
    rcases (norm_nonneg (aeval α Q)).eq_or_lt with h0 | hvQ
    · rw [← h0]; exact Real.exp_pos _
    have hsm : e * Real.log ‖aeval α Q‖ + Real.log ‖aeval α R‖ < Real.log H * (-(lam * n)) := by
      have h : ‖aeval α Q‖ ^ e * ‖aeval α R‖ < Real.exp (Real.log H * (-(lam * n))) := by
        rw [← Real.rpow_def_of_pos hH0]
        calc _ = ‖aeval α P‖ := by rw [hPeq, map_mul, map_pow, norm_mul, norm_pow]
          _ < _ := hsmall
      have h' := Real.log_lt_log (by positivity) h
      rwa [Real.log_mul (by positivity) hvR.ne', Real.log_pow, Real.log_exp] at h'
    have hK : (Q.natDegree * R.natDegree : ℝ) * Real.log 2 + R.natDegree * Real.log MQ +
        Q.natDegree * Real.log MR ≤ 5 * n * Real.log H := by
      have h1 : (Q.natDegree * R.natDegree : ℝ) ≤ n * Real.log H :=
        mul_le_mul (hδ.trans hdeg) (hr.trans (hdeg.trans hlog)) (Nat.cast_nonneg _) hn0
      have h2 : (R.natDegree : ℝ) * Real.log MQ ≤ n * (2 * Real.log H) :=
        mul_le_mul (hr.trans hdeg) (by linarith) ha hn0
      have h3 : (Q.natDegree : ℝ) * Real.log MR ≤ n * (2 * Real.log H) :=
        mul_le_mul (hδ.trans hdeg) (by linarith) hb hn0
      nlinarith [mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ Q.natDegree * R.natDegree)]
    rw [← Real.log_lt_iff_lt_exp hvQ,
      show Real.log H * -((lam - 6) * n / e) = -((lam - 6) * n * Real.log H) / e by ring,
      lt_div_iff₀ he']
    linarith [mul_nonneg hn0 hL0]
  · -- the coefficients
    have hc := norm_coeff_le_choose_mul_mahlerMeasure i (Q.map (Int.castRingHom ℂ))
    rw [natDegree_map_eq_of_injective Int.cast_injective, coeff_map, eq_intCast,
      Complex.norm_intCast] at hc
    have hch : ((Q.natDegree.choose i : ℕ) : ℝ) ≤ 2 ^ Q.natDegree := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    refine hc.trans ((mul_le_mul_of_nonneg_right hch (by positivity)).trans ?_)
    have h2 : (2 : ℝ) ^ Q.natDegree * MQ = Real.exp (Q.natDegree * Real.log 2 + Real.log MQ) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log two_pos, Real.exp_log (by positivity)]
    rw [h2, Real.rpow_def_of_pos hH0, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [show Real.log H * (1 / e) + 2 * n / e = (Real.log H + 2 * n) / e by ring, le_div_iff₀ he',
      show (Q.natDegree * Real.log 2 + Real.log MQ) * e =
        e * Q.natDegree * Real.log 2 + e * Real.log MQ by ring]
    linarith [mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ e * Q.natDegree) hl2]
  · -- the degree
    rw [le_div_iff₀ he']
    linarith

#print axioms solution
