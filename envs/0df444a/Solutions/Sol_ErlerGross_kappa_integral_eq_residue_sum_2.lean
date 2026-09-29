-- Prove2me | solution 2 for ErlerGross.kappa_integral_eq_residue_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T19:53:14.335107+00:00
-- url     : https://prove2.me/submissions/4ee5996c-6cdd-4245-9968-39b7ebdadfc6

import Mathlib
import Definitions.Def_ErlerGross_defs

set_option autoImplicit false

open Real Filter Topology MeasureTheory Set

theorem egf80_harm_diff_tendsto (k c : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((harmonic (k * N + c) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ))
      atTop (𝓝 (Real.log k)) := by
  have hkN : Tendsto (fun N : ℕ => k * N + c) atTop atTop := by
    apply tendsto_atTop_mono (fun N => (by nlinarith : N ≤ k * N + c))
    exact tendsto_id
  have h1 := tendsto_harmonic_sub_log_add_one.comp hkN
  have h2 := tendsto_harmonic_sub_log_add_one
  have h3 : Tendsto (fun N : ℕ => Real.log ((k : ℝ) + ((c : ℝ) + 1 - k) * (1 / ((N : ℝ) + 1))))
      atTop (𝓝 (Real.log k)) := by
    have hk0 : (k : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ((c : ℝ) + 1 - k)).const_add (k : ℝ)
    rw [mul_zero, add_zero] at this
    exact this.log hk0
  have hsum := (h1.sub h2).add h3
  rw [sub_self, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards with N
  simp only [Function.comp]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have harg : (k : ℝ) + ((c : ℝ) + 1 - k) * (1 / ((N : ℝ) + 1)) =
      ((((k * N + c : ℕ) : ℝ) + 1)) / ((N : ℝ) + 1) := by
    push_cast
    field_simp
    ring
  rw [harg, Real.log_div (by positivity) (by positivity)]
  ring

theorem egf80_term (n : ℕ) :
    ErlerGross.b3Term (n + 1) =
      -2 / ((2 * (n : ℝ) + 1) * (6 * (n : ℝ) + 2) * (6 * (n : ℝ) + 4)) := by
  unfold ErlerGross.b3Term
  push_cast
  have h1 : (2 * ((n : ℝ) + 1) - 1) = 2 * (n : ℝ) + 1 := by ring
  have h2 : (2 * ((n : ℝ) + 1) - 2 / 3) = (6 * (n : ℝ) + 4) / 3 := by ring
  have h3 : (2 * ((n : ℝ) + 1) - 4 / 3) = (6 * (n : ℝ) + 2) / 3 := by ring
  rw [h1, h2, h3]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have a1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have a2 : (6 * (n : ℝ) + 2) ≠ 0 := by positivity
  have a3 : (6 * (n : ℝ) + 4) ≠ 0 := by positivity
  field_simp
  ring

theorem egf80_partial (N : ℕ) :
    ∑ n ∈ Finset.range N, ErlerGross.b3Term (n + 1) =
      -(3 / 2) * (((harmonic (3 * N + 0) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ)) +
        2 * (((harmonic (2 * N + 0) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ)) := by
  induction N with
  | zero => simp [harmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, egf80_term]
    have e3 : 3 * (N + 1) + 0 = (3 * N + 0) + 1 + 1 + 1 := by ring
    have e2 : 2 * (N + 1) + 0 = (2 * N + 0) + 1 + 1 := by ring
    rw [e3, e2, harmonic_succ N, harmonic_succ (3 * N + 0 + 1 + 1), harmonic_succ (3 * N + 0 + 1),
      harmonic_succ (3 * N + 0), harmonic_succ (2 * N + 0 + 1), harmonic_succ (2 * N + 0)]
    push_cast
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have a1 : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
    have a2 : (6 * (N : ℝ) + 2) ≠ 0 := by positivity
    have a3 : (6 * (N : ℝ) + 4) ≠ 0 := by positivity
    have b1 : (3 * (N : ℝ) + 0 + 1) ≠ 0 := by positivity
    have b2 : (3 * (N : ℝ) + 0 + 1 + 1) ≠ 0 := by positivity
    have b3 : (3 * (N : ℝ) + 0 + 1 + 1 + 1) ≠ 0 := by positivity
    have c1 : (2 * (N : ℝ) + 0 + 1) ≠ 0 := by positivity
    have c2 : (2 * (N : ℝ) + 0 + 1 + 1) ≠ 0 := by positivity
    have d1 : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

theorem egf80_B3 :
    HasSum (fun n : ℕ => ErlerGross.b3Term (n + 1)) (-Real.log (27 / 16) / 2) := by
  have hnn : ∀ n : ℕ, 0 ≤ -ErlerGross.b3Term (n + 1) := by
    intro n
    rw [egf80_term]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (0 : ℝ) < (2 * (n : ℝ) + 1) * (6 * (n : ℝ) + 2) * (6 * (n : ℝ) + 4) := by positivity
    rw [neg_div, neg_neg]
    positivity
  have key : HasSum (fun n : ℕ => -ErlerGross.b3Term (n + 1)) (Real.log (27 / 16) / 2) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    have h3 := egf80_harm_diff_tendsto 3 0 (by norm_num)
    have h2 := egf80_harm_diff_tendsto 2 0 (by norm_num)
    have h := ((h3.const_mul (3 / 2)).sub (h2.const_mul 2))
    have hval : 3 / 2 * Real.log ((3 : ℕ) : ℝ) - 2 * Real.log ((2 : ℕ) : ℝ) =
        Real.log (27 / 16) / 2 := by
      have e : (27 / 16 : ℝ) = 3 ^ 3 / 2 ^ 4 := by norm_num
      rw [e, Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards with N
    rw [Finset.sum_neg_distrib, egf80_partial]
    ring
  have := key.neg
  rw [neg_div]
  simpa only [neg_neg] using this

theorem egf80_frullani (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    IntegrableOn (fun x : ℝ => x⁻¹ * (Real.exp (-(p * x)) - Real.exp (-(q * x)))) (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), x⁻¹ * (Real.exp (-(p * x)) - Real.exp (-(q * x))) = Real.log (q / p) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hint : IntegrableOn (fun x : ℝ => x⁻¹ * (Real.exp (-(p * x)) - Real.exp (-(q * x))))
      (Ioi 0) := by
    have hg : IntegrableOn (fun x : ℝ => (q - p) * Real.exp (-p * x)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith : -p < 0) 0).const_mul (q - p)
    refine hg.mono' (by fun_prop : Measurable fun x : ℝ =>
      x⁻¹ * (Real.exp (-(p * x)) - Real.exp (-(q * x)))).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    have h1 : 0 ≤ Real.exp (-(p * x)) - Real.exp (-(q * x)) := by
      have : Real.exp (-(q * x)) ≤ Real.exp (-(p * x)) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have h2 : Real.exp (-(p * x)) - Real.exp (-(q * x)) ≤ (q - p) * x * Real.exp (-(p * x)) := by
      have e : Real.exp (-(q * x)) = Real.exp (-(p * x)) * Real.exp (-((q - p) * x)) := by
        rw [← Real.exp_add]; congr 1; ring
      have := Real.add_one_le_exp (-((q - p) * x))
      rw [e]
      have hE := Real.exp_pos (-(p * x))
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hx0.le) h1),
      inv_mul_le_iff₀ hx0]
    have : -p * x = -(p * x) := by ring
    rw [this]
    linarith
  refine ⟨hint, ?_⟩
  have h := Frullani.integral_Ioi_eq (f := fun x : ℝ => Real.exp (-x)) (a := p) (b := q)
    (L := 1) (R := 0)
    ((Real.continuous_exp.comp continuous_neg).locallyIntegrable.locallyIntegrableOn _) hp hq
    (((Real.continuous_exp.comp continuous_neg).tendsto' 0 1 (by simp)).mono_left
      nhdsWithin_le_nhds)
    Real.tendsto_exp_neg_atTop_nhds_zero (by simpa [smul_eq_mul] using hint)
  simpa [smul_eq_mul] using h

noncomputable def egf80W (x : ℝ) : ℝ :=
  x⁻¹ * ((Real.cosh x - 1) / ((1 + 2 * Real.cosh x) * Real.sinh x))

theorem egf80_form (x : ℝ) (hx : 0 < x) :
    (Real.cosh x - 1) / ((1 + 2 * Real.cosh x) * Real.sinh x) =
      Real.exp (-x) * (1 - Real.exp (-x)) /
        ((1 + Real.exp (-x)) * (1 + Real.exp (-x) + Real.exp (-x) ^ 2)) := by
  obtain ⟨q, hq⟩ : ∃ q, q = Real.exp (-x) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ Real.exp_pos _
  have hq1 : q < 1 := hq ▸ Real.exp_lt_one_iff.mpr (by linarith)
  have hE : Real.exp x = q⁻¹ := by rw [hq, Real.exp_neg, inv_inv]
  rw [Real.cosh_eq, Real.sinh_eq, hE, ← hq]
  have h1 : q⁻¹ - q ≠ 0 := by
    have : 1 < q⁻¹ := one_lt_inv₀ hq0 |>.mpr hq1
    linarith
  have h2 : (1 + q) ≠ 0 := by positivity
  have h3 : (1 + q + q ^ 2) ≠ 0 := by positivity
  have h4 : q ≠ 0 := hq0.ne'
  have h5 : 1 - q ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem egf80_key (x : ℝ) (hx : 0 < x) :
    (Real.cosh x - 1) / ((1 + 2 * Real.cosh x) * Real.sinh x) * (1 - Real.exp (-(6 * x))) =
      Real.exp (-(1 * x)) - 3 * Real.exp (-(2 * x)) + 4 * Real.exp (-(3 * x)) -
        3 * Real.exp (-(4 * x)) + Real.exp (-(5 * x)) := by
  rw [egf80_form x hx]
  have e : ∀ n : ℕ, Real.exp (-((n : ℝ) * x)) = Real.exp (-x) ^ n := by
    intro n; rw [← Real.exp_nat_mul]; congr 1; ring
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  have e5 := e 5
  have e6 := e 6
  push_cast at e1 e2 e3 e4 e5 e6
  rw [e1, e2, e3, e4, e5, e6]
  have hq0 : 0 < Real.exp (-x) := Real.exp_pos _
  have h2 : (1 + Real.exp (-x)) ≠ 0 := by positivity
  have h3 : (1 + Real.exp (-x) + Real.exp (-x) ^ 2) ≠ 0 := by positivity
  field_simp
  ring

theorem egf80_expand (x : ℝ) (hx : 0 < x) (N : ℕ) :
    egf80W x =
      ∑ k ∈ Finset.range N, x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 1) * x)) -
          3 * Real.exp (-((6 * (k : ℝ) + 2) * x)) + 4 * Real.exp (-((6 * (k : ℝ) + 3) * x)) -
          3 * Real.exp (-((6 * (k : ℝ) + 4) * x)) + Real.exp (-((6 * (k : ℝ) + 5) * x))) +
        Real.exp (-(6 * (N : ℝ) * x)) * egf80W x := by
  have hkey := egf80_key x hx
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have ee : ∀ i : ℝ, Real.exp (-((6 * (N : ℝ) + i) * x)) =
        Real.exp (-(6 * (N : ℝ) * x)) * Real.exp (-(i * x)) := by
      intro i; rw [← Real.exp_add]; congr 1; ring
    have e6 : Real.exp (-(6 * ((N + 1 : ℕ) : ℝ) * x)) =
        Real.exp (-(6 * (N : ℝ) * x)) * Real.exp (-(6 * x)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [ee 1, ee 2, ee 3, ee 4, ee 5, e6]
    unfold egf80W at ih ⊢
    linear_combination ih + (Real.exp (-(6 * (N : ℝ) * x)) * x⁻¹) * hkey

theorem egf80_W_bound (x : ℝ) (hx : 0 < x) : 0 ≤ egf80W x ∧ egf80W x ≤ Real.exp (-x) := by
  unfold egf80W
  rw [egf80_form x hx]
  obtain ⟨q, hq⟩ : ∃ q, q = Real.exp (-x) := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : 0 < q := hq ▸ Real.exp_pos _
  have hq1 : q < 1 := hq ▸ Real.exp_lt_one_iff.mpr (by linarith)
  have hlin : 1 - q ≤ x := by
    have := Real.add_one_le_exp (-x)
    rw [← hq] at this
    linarith
  have hden : 1 ≤ (1 + q) * (1 + q + q ^ 2) := by nlinarith
  have hnum : 0 ≤ q * (1 - q) := by nlinarith
  have hfr : q * (1 - q) / ((1 + q) * (1 + q + q ^ 2)) ≤ q * (1 - q) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hfr0 : 0 ≤ q * (1 - q) / ((1 + q) * (1 + q + q ^ 2)) := by positivity
  refine ⟨mul_nonneg (inv_nonneg.mpr hx.le) hfr0, ?_⟩
  calc x⁻¹ * (q * (1 - q) / ((1 + q) * (1 + q + q ^ 2))) ≤ x⁻¹ * (q * (1 - q)) :=
        mul_le_mul_of_nonneg_left hfr (inv_nonneg.mpr hx.le)
    _ ≤ q := by
        rw [inv_mul_le_iff₀ hx]
        nlinarith

theorem egf80_W_meas : Measurable egf80W := by
  unfold egf80W
  fun_prop

theorem egf80_W_int : IntegrableOn egf80W (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  refine hg.mono' egf80_W_meas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have := egf80_W_bound x hx
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

theorem egf80_term_int (k : ℕ) :
    IntegrableOn (fun x : ℝ => x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 1) * x)) -
          3 * Real.exp (-((6 * (k : ℝ) + 2) * x)) + 4 * Real.exp (-((6 * (k : ℝ) + 3) * x)) -
          3 * Real.exp (-((6 * (k : ℝ) + 4) * x)) + Real.exp (-((6 * (k : ℝ) + 5) * x)))) (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 1) * x)) -
          3 * Real.exp (-((6 * (k : ℝ) + 2) * x)) + 4 * Real.exp (-((6 * (k : ℝ) + 3) * x)) -
          3 * Real.exp (-((6 * (k : ℝ) + 4) * x)) + Real.exp (-((6 * (k : ℝ) + 5) * x))) =
      Real.log ((6 * (k : ℝ) + 3) / (6 * (k : ℝ) + 1)) -
        3 * Real.log ((6 * (k : ℝ) + 3) / (6 * (k : ℝ) + 2)) +
        3 * Real.log ((6 * (k : ℝ) + 4) / (6 * (k : ℝ) + 3)) -
        Real.log ((6 * (k : ℝ) + 5) / (6 * (k : ℝ) + 3)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨i13, v13⟩ := egf80_frullani (6 * (k : ℝ) + 1) (6 * (k : ℝ) + 3) (by positivity)
    (by linarith)
  obtain ⟨i23, v23⟩ := egf80_frullani (6 * (k : ℝ) + 2) (6 * (k : ℝ) + 3) (by positivity)
    (by linarith)
  obtain ⟨i34, v34⟩ := egf80_frullani (6 * (k : ℝ) + 3) (6 * (k : ℝ) + 4) (by positivity)
    (by linarith)
  obtain ⟨i35, v35⟩ := egf80_frullani (6 * (k : ℝ) + 3) (6 * (k : ℝ) + 5) (by positivity)
    (by linarith)
  have hf : (fun x : ℝ => x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 1) * x)) -
          3 * Real.exp (-((6 * (k : ℝ) + 2) * x)) + 4 * Real.exp (-((6 * (k : ℝ) + 3) * x)) -
          3 * Real.exp (-((6 * (k : ℝ) + 4) * x)) + Real.exp (-((6 * (k : ℝ) + 5) * x)))) =
      fun x : ℝ =>
        (x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 1) * x)) - Real.exp (-((6 * (k : ℝ) + 3) * x))) -
          3 * (x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 2) * x)) -
            Real.exp (-((6 * (k : ℝ) + 3) * x))))) +
        (3 * (x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 3) * x)) -
            Real.exp (-((6 * (k : ℝ) + 4) * x)))) -
          x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 3) * x)) - Real.exp (-((6 * (k : ℝ) + 5) * x)))) := by
    funext x; ring
  rw [hf]
  have j1 : IntegrableOn (fun x : ℝ =>
      x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 1) * x)) - Real.exp (-((6 * (k : ℝ) + 3) * x))) -
          3 * (x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 2) * x)) -
            Real.exp (-((6 * (k : ℝ) + 3) * x))))) (Ioi 0) := i13.sub (i23.const_mul 3)
  have j2 : IntegrableOn (fun x : ℝ =>
      3 * (x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 3) * x)) -
            Real.exp (-((6 * (k : ℝ) + 4) * x)))) -
          x⁻¹ * (Real.exp (-((6 * (k : ℝ) + 3) * x)) - Real.exp (-((6 * (k : ℝ) + 5) * x))))
      (Ioi 0) := (i34.const_mul 3).sub i35
  refine ⟨j1.add j2, ?_⟩
  rw [integral_add j1 j2, integral_sub i13 (i23.const_mul 3), integral_sub (i34.const_mul 3) i35,
    integral_const_mul, integral_const_mul, v13, v23, v34, v35]
  ring

theorem egf80_T (k : ℕ) :
    Real.log ((6 * (k : ℝ) + 3) / (6 * (k : ℝ) + 1)) -
        3 * Real.log ((6 * (k : ℝ) + 3) / (6 * (k : ℝ) + 2)) +
        3 * Real.log ((6 * (k : ℝ) + 4) / (6 * (k : ℝ) + 3)) -
        Real.log ((6 * (k : ℝ) + 5) / (6 * (k : ℝ) + 3)) =
      3 * Real.log (1 - (1 / 3 : ℝ) ^ 2 / (2 * (k : ℝ) + 1) ^ 2) -
        Real.log (1 - (2 / 3 : ℝ) ^ 2 / (2 * (k : ℝ) + 1) ^ 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have p1 : (0 : ℝ) < 6 * k + 1 := by positivity
  have p2 : (0 : ℝ) < 6 * k + 2 := by positivity
  have p3 : (0 : ℝ) < 6 * k + 3 := by positivity
  have p4 : (0 : ℝ) < 6 * k + 4 := by positivity
  have p5 : (0 : ℝ) < 6 * k + 5 := by positivity
  have hm : (0 : ℝ) < 2 * k + 1 := by positivity
  have a1 : 1 - (1 / 3 : ℝ) ^ 2 / (2 * (k : ℝ) + 1) ^ 2 =
      ((6 * (k : ℝ) + 2) * (6 * (k : ℝ) + 4)) / (6 * (k : ℝ) + 3) ^ 2 := by
    field_simp; ring
  have a2 : 1 - (2 / 3 : ℝ) ^ 2 / (2 * (k : ℝ) + 1) ^ 2 =
      ((6 * (k : ℝ) + 1) * (6 * (k : ℝ) + 5)) / (6 * (k : ℝ) + 3) ^ 2 := by
    field_simp; ring
  have l1 : Real.log (((6 * (k : ℝ) + 2) * (6 * (k : ℝ) + 4)) / (6 * (k : ℝ) + 3) ^ 2) =
      Real.log (6 * (k : ℝ) + 2) + Real.log (6 * (k : ℝ) + 4) - 2 * Real.log (6 * (k : ℝ) + 3) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul p2.ne' p4.ne', Real.log_pow]
    push_cast; ring
  have l2 : Real.log (((6 * (k : ℝ) + 1) * (6 * (k : ℝ) + 5)) / (6 * (k : ℝ) + 3) ^ 2) =
      Real.log (6 * (k : ℝ) + 1) + Real.log (6 * (k : ℝ) + 5) - 2 * Real.log (6 * (k : ℝ) + 3) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul p1.ne' p5.ne', Real.log_pow]
    push_cast; ring
  rw [a1, a2, l1, l2, Real.log_div p3.ne' p1.ne', Real.log_div p3.ne' p2.ne',
    Real.log_div p4.ne' p3.ne', Real.log_div p5.ne' p3.ne']
  ring

theorem egf80_cosprod (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    Tendsto (fun N : ℕ => ∏ k ∈ Finset.range N, (1 - z ^ 2 / (2 * (k : ℝ) + 1) ^ 2)) atTop
      (𝓝 (Real.cos (π * z / 2))) := by
  have hsplit : ∀ N : ℕ, ∏ j ∈ Finset.range (2 * N), ((1 : ℝ) - z ^ 2 / ((j : ℝ) + 1) ^ 2) =
      (∏ k ∈ Finset.range N, (1 - z ^ 2 / (2 * (k : ℝ) + 1) ^ 2)) *
        ∏ j ∈ Finset.range N, ((1 : ℝ) - (z / 2) ^ 2 / ((j : ℝ) + 1) ^ 2) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.prod_range_succ,
        Finset.prod_range_succ, ih, Finset.prod_range_succ, Finset.prod_range_succ]
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have c1 : z ^ 2 / (((2 * N + 1 : ℕ) : ℝ) + 1) ^ 2 = (z / 2) ^ 2 / ((N : ℝ) + 1) ^ 2 := by
        push_cast
        have : (N : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      have c2 : z ^ 2 / (((2 * N : ℕ) : ℝ) + 1) ^ 2 = z ^ 2 / (2 * (N : ℝ) + 1) ^ 2 := by
        push_cast; ring
      rw [c1, c2]
      ring
  have hfac : ∀ N : ℕ, ∏ j ∈ Finset.range N, ((1 : ℝ) - (z / 2) ^ 2 / ((j : ℝ) + 1) ^ 2) ≠ 0 := by
    intro N
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have : (z / 2) ^ 2 / ((j : ℝ) + 1) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    linarith
  have htwo : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun c => ⟨c, fun M hM => by omega⟩)
  have h1 := (Real.tendsto_euler_sin_prod z).comp htwo
  have h2 := (Real.tendsto_euler_sin_prod (z / 2)).const_mul 2
  have hs : Real.sin (π * (z / 2)) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
  have hlim := h1.div h2 (mul_ne_zero two_ne_zero hs)
  have hval : Real.sin (π * z) / (2 * Real.sin (π * (z / 2))) = Real.cos (π * z / 2) := by
    rw [show π * z = 2 * (π * (z / 2)) by ring, Real.sin_two_mul]
    rw [show π * (z / 2) = π * z / 2 by ring]
    have : Real.sin (π * z / 2) ≠ 0 := by rwa [show π * z / 2 = π * (z / 2) by ring]
    field_simp
  rw [hval] at hlim
  refine hlim.congr (fun N => ?_)
  show (π * z * ∏ j ∈ Finset.range (2 * N), ((1 : ℝ) - z ^ 2 / ((j : ℝ) + 1) ^ 2)) /
      (2 * (π * (z / 2) * ∏ j ∈ Finset.range N, ((1 : ℝ) - (z / 2) ^ 2 / ((j : ℝ) + 1) ^ 2))) = _
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hz : z / 2 ≠ 0 := by positivity
  rw [hsplit N, div_eq_iff (mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hpi hz) (hfac N)))]
  ring

theorem egf80_W_integral : ∫ x in Ioi (0 : ℝ), egf80W x = Real.log (27 / 16) / 2 := by
  obtain ⟨S, hSd⟩ : ∃ S : ℕ → ℝ, S = fun N : ℕ => ∑ k ∈ Finset.range N,
      (Real.log ((6 * (k : ℝ) + 3) / (6 * (k : ℝ) + 1)) -
        3 * Real.log ((6 * (k : ℝ) + 3) / (6 * (k : ℝ) + 2)) +
        3 * Real.log ((6 * (k : ℝ) + 4) / (6 * (k : ℝ) + 3)) -
        Real.log ((6 * (k : ℝ) + 5) / (6 * (k : ℝ) + 3))) := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R : ℕ → ℝ, R = fun N : ℕ => ∫ x in Ioi (0 : ℝ),
      Real.exp (-(6 * (N : ℝ) * x)) * egf80W x := ⟨_, rfl⟩
  have hbound : ∀ N : ℕ, ∀ x ∈ Ioi (0 : ℝ),
      ‖Real.exp (-(6 * (N : ℝ) * x)) * egf80W x‖ ≤ ‖egf80W x‖ := by
    intro N x hx
    have hx' : (0 : ℝ) < x := hx
    rw [norm_mul]
    have : ‖Real.exp (-(6 * (N : ℝ) * x))‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : 0 ≤ 6 * (N : ℝ) * x := by positivity
      linarith
    calc _ ≤ 1 * ‖egf80W x‖ := by gcongr
      _ = _ := one_mul _
  have hFint : ∀ N : ℕ, IntegrableOn (fun x : ℝ => Real.exp (-(6 * (N : ℝ) * x)) * egf80W x)
      (Ioi 0) := by
    intro N
    refine egf80_W_int.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      egf80_W_int.aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (hbound N))
  have hId : ∀ N : ℕ, (∫ x in Ioi (0 : ℝ), egf80W x) = S N + R N := by
    intro N
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => egf80_expand x hx N)]
    rw [integral_add (integrable_finsetSum _ (fun k _ => (egf80_term_int k).1)) (hFint N)]
    rw [MeasureTheory.integral_finsetSum _ (fun k _ => (egf80_term_int k).1), hSd, hRd]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => (egf80_term_int k).2)
  have hR : Tendsto R atTop (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun (N : ℕ) (x : ℝ) => Real.exp (-(6 * (N : ℝ) * x)) * egf80W x)
      (f := fun _ => (0 : ℝ)) (fun x => ‖egf80W x‖)
      (fun N => (hFint N).aestronglyMeasurable) egf80_W_int.norm
      (fun N => (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (hbound N))) ?_
    · rw [hRd]; simpa using h
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have hx' : (0 : ℝ) < x := hx
      have heq : ∀ N : ℕ, Real.exp (-(6 * (N : ℝ) * x)) * egf80W x =
          (Real.exp (-6 * x)) ^ N * egf80W x := by
        intro N
        rw [← Real.exp_nat_mul]
        congr 2
        ring
      simp_rw [heq]
      have hq : Real.exp (-6 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hq).mul_const
        (egf80W x)
  have hS : Tendsto S atTop (𝓝 (∫ x in Ioi (0 : ℝ), egf80W x)) := by
    have := (tendsto_const_nhds (x := ∫ x in Ioi (0 : ℝ), egf80W x)).sub hR
    rw [sub_zero] at this
    refine this.congr (fun N => ?_)
    rw [hId N]; ring
  have hS2 : Tendsto S atTop (𝓝 (Real.log (27 / 16) / 2)) := by
    have hp1 := egf80_cosprod (1 / 3) (by norm_num) (by norm_num)
    have hp2 := egf80_cosprod (2 / 3) (by norm_num) (by norm_num)
    have c1 : Real.cos (π * (1 / 3) / 2) = √3 / 2 := by
      rw [show π * (1 / 3) / 2 = π / 6 by ring, Real.cos_pi_div_six]
    have c2 : Real.cos (π * (2 / 3) / 2) = 1 / 2 := by
      rw [show π * (2 / 3) / 2 = π / 3 by ring, Real.cos_pi_div_three]
    rw [c1] at hp1
    rw [c2] at hp2
    have hlim := ((hp1.log (by positivity)).const_mul 3).sub (hp2.log (by norm_num))
    have hval : 3 * Real.log (√3 / 2) - Real.log (1 / 2) = Real.log (27 / 16) / 2 := by
      have e : (27 / 16 : ℝ) = 3 ^ 3 / 2 ^ 4 := by norm_num
      rw [e, Real.log_div (by positivity) (by norm_num), Real.log_div (by norm_num) (by norm_num),
        Real.log_div (by norm_num) (by norm_num), Real.log_sqrt (by norm_num), Real.log_pow,
        Real.log_pow, Real.log_one]
      push_cast
      ring
    rw [hval] at hlim
    refine hlim.congr (fun N => ?_)
    have hpos : ∀ (z : ℝ), 0 < z → z < 1 → ∀ k ∈ Finset.range N,
        (1 - z ^ 2 / (2 * (k : ℝ) + 1) ^ 2) ≠ 0 := by
      intro z hz0 hz1 k _
      have hk : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have : z ^ 2 / (2 * (k : ℝ) + 1) ^ 2 < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith
      linarith
    rw [Real.log_prod (hpos (1 / 3) (by norm_num) (by norm_num)),
      Real.log_prod (hpos (2 / 3) (by norm_num) (by norm_num)), hSd, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => (egf80_T k).symm)
  exact tendsto_nhds_unique hS hS2

theorem egf80_even (κ : ℝ) : ErlerGross.kappaIntegrand |κ| = ErlerGross.kappaIntegrand κ := by
  rcases le_or_gt 0 κ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    unfold ErlerGross.kappaIntegrand
    rw [show π * -κ / 2 = -(π * κ / 2) by ring, Real.cosh_neg, Real.sinh_neg]
    ring

theorem egf80_kappa_integral : ∫ κ, ErlerGross.kappaIntegrand κ = -Real.log (27 / 16) / 2 := by
  have h1 : ∫ κ, ErlerGross.kappaIntegrand κ = 2 * ∫ κ in Ioi (0 : ℝ), ErlerGross.kappaIntegrand κ := by
    rw [← integral_comp_abs]
    congr 1
    funext κ
    rw [egf80_even]
  have h2 : ∫ κ in Ioi (0 : ℝ), ErlerGross.kappaIntegrand κ =
      ∫ κ in Ioi (0 : ℝ), (-(π / 4)) * egf80W ((π / 2) * κ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun κ hκ => ?_)
    have hκ' : (0 : ℝ) < κ := hκ
    unfold ErlerGross.kappaIntegrand egf80W
    rw [show π * κ / 2 = π / 2 * κ by ring]
    have hpi : π ≠ 0 := Real.pi_ne_zero
    have hk : κ ≠ 0 := hκ'.ne'
    field_simp
    ring
  have h3 : ∫ κ in Ioi (0 : ℝ), (-(π / 4)) * egf80W ((π / 2) * κ) =
      -(1 / 2) * ∫ x in Ioi (0 : ℝ), egf80W x := by
    rw [integral_const_mul, integral_comp_mul_left_Ioi egf80W 0 (by positivity), mul_zero,
      smul_eq_mul]
    have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [h1, h2, h3, egf80_W_integral]
  ring

open Real Filter Topology MeasureTheory ErlerGross in
theorem solution :
    HasSum (fun n : ℕ => b3Term (n + 1)) (∫ κ, kappaIntegrand κ) := by
  rw [egf80_kappa_integral]
  exact egf80_B3
