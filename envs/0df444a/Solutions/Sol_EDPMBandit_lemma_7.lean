-- Prove2me | solution 1 for EDPMBandit.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:18:48.621787+00:00
-- url     : https://prove2.me/submissions/cfcb09fc-4b14-4724-b82e-be5574809f35

import Mathlib

open MeasureTheory Filter

theorem solution (a : ℝ) (ha : 0 < a) (m : ℕ) :
    (∫ x in Set.Ioi (1 : ℝ), x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2))) =
        Real.exp (-a) / (2 * a ^ (m + 1)) *
          ∑ j ∈ Finset.range (m + 1), ((m.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j ∧
      (3 ≤ a →
        (∫ x in Set.Ioi (1 : ℝ), x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2))) ≤
          (m.factorial : ℝ) * Real.exp (-a) / 2) := by
  have ha' : a ≠ 0 := ha.ne'
  let I : ℕ → ℝ := fun m => ∫ x in Set.Ioi (1 : ℝ), x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2))
  change I m = Real.exp (-a) / (2 * a ^ (m + 1)) *
          ∑ j ∈ Finset.range (m + 1), ((m.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j ∧
      (3 ≤ a → I m ≤ (m.factorial : ℝ) * Real.exp (-a) / 2)
  have hint_pow : ∀ n : ℕ, IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-(a * x ^ 2)))
      (Set.Ioi (1 : ℝ)) := by
    intro n
    have hn : (-1 : ℝ) < (n : ℝ) := by
      have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h := (integrableOn_rpow_mul_exp_neg_mul_sq ha (s := (n : ℝ)) hn).mono_set
      (Set.Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp [Real.rpow_natCast]
  have htend_pow : ∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (-(a * x ^ 2))) atTop (nhds 0) := by
    intro n
    have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (s := (n : ℝ))).mono_left
      atTop_le_cocompact
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [abs_of_nonneg hx, Real.rpow_natCast]
    ring
  have hderiv_v : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))
      (x * Real.exp (-(a * x ^ 2))) x := by
    intro x
    have hpoly : HasDerivAt (fun y : ℝ => -(a * y ^ 2)) (-(a * (2 * x))) x := by
      have h1 : HasDerivAt (fun y : ℝ => y ^ 2) ((2 : ℝ) * x ^ (2 - 1)) x := hasDerivAt_pow 2 x
      have h2 : HasDerivAt (fun y : ℝ => a * y ^ 2) (a * ((2 : ℝ) * x ^ (2 - 1))) x :=
        h1.const_mul a
      have h3 : HasDerivAt (fun y : ℝ => -(a * y ^ 2)) (-(a * ((2 : ℝ) * x ^ (2 - 1)))) x :=
        h2.neg
      convert h3 using 1
      ring
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(a * y ^ 2)))
        (Real.exp (-(a * x ^ 2)) * (-(a * (2 * x)))) x := hpoly.exp
    have h4 : HasDerivAt (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))
        (-(2 * a)⁻¹ * (Real.exp (-(a * x ^ 2)) * (-(a * (2 * x))))) x := hexp.const_mul _
    convert h4 using 1
    field_simp
  have hbase : I 0 = Real.exp (-a) / (2 * a) := by
    have h0 : I 0 = ∫ x in Set.Ioi (1 : ℝ), x * Real.exp (-(a * x ^ 2)) := by
      show (∫ x in Set.Ioi (1 : ℝ), x ^ (2 * 0 + 1) * Real.exp (-(a * x ^ 2))) = _
      norm_num
    rw [h0]
    have hderiv : ∀ x ∈ Set.Ici (1 : ℝ),
        HasDerivAt (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))
          (x * Real.exp (-(a * x ^ 2))) x := fun x _ => hderiv_v x
    have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(a * x ^ 2))) (Set.Ioi (1 : ℝ)) := by
      have h := hint_pow 1
      refine h.congr_fun ?_ measurableSet_Ioi
      intro x _
      simp
    have htend : Tendsto (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2))) atTop (nhds 0) := by
      have h := (htend_pow 0).const_mul (-(2 * a)⁻¹)
      simpa using h
    have key := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (1 : ℝ))
      (f := fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))
      (f' := fun x : ℝ => x * Real.exp (-(a * x ^ 2))) (m := 0) hderiv hint htend
    rw [key]
    norm_num
    field_simp
  have hrec : ∀ m : ℕ, I (m + 1) = Real.exp (-a) / (2 * a) + ((m + 1 : ℝ) / a) * I m := by
    intro m
    have hI_succ : I (m + 1) = ∫ x in Set.Ioi (1 : ℝ),
        x ^ (2 * m + 2) * (x * Real.exp (-(a * x ^ 2))) := by
      show (∫ x in Set.Ioi (1 : ℝ), x ^ (2 * (m + 1) + 1) * Real.exp (-(a * x ^ 2))) = _
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x _
      change x ^ (2 * (m + 1) + 1) * Real.exp (-(a * x ^ 2)) =
        x ^ (2 * m + 2) * (x * Real.exp (-(a * x ^ 2)))
      rw [show 2 * (m + 1) + 1 = 2 * m + 2 + 1 by ring, pow_succ]
      ring
    have hderiv_u : ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivAt (fun y : ℝ => y ^ (2 * m + 2)) ((2 * m + 2 : ℝ) * x ^ (2 * m + 1)) x := by
      intro x _
      simpa using hasDerivAt_pow (2 * m + 2) x
    have hderiv_v' : ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivAt (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))
          (x * Real.exp (-(a * x ^ 2))) x := fun x _ => hderiv_v x
    have huv' : IntegrableOn ((fun y : ℝ => y ^ (2 * m + 2)) *
        (fun y : ℝ => y * Real.exp (-(a * y ^ 2)))) (Set.Ioi (1 : ℝ)) := by
      have h := hint_pow (2 * m + 3)
      refine h.congr_fun ?_ measurableSet_Ioi
      intro x _
      simp only [Pi.mul_apply]
      show x ^ (2 * m + 3) * Real.exp (-(a * x ^ 2)) =
        x ^ (2 * m + 2) * (x * Real.exp (-(a * x ^ 2)))
      rw [show 2 * m + 3 = 2 * m + 2 + 1 by ring, pow_succ]
      ring
    have hu'v : IntegrableOn ((fun y : ℝ => (2 * m + 2 : ℝ) * y ^ (2 * m + 1)) *
        (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))) (Set.Ioi (1 : ℝ)) := by
      have hbase_int : Integrable (fun x : ℝ => x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2)))
          (volume.restrict (Set.Ioi (1 : ℝ))) := hint_pow (2 * m + 1)
      have h : IntegrableOn (fun x : ℝ => -((2 * m + 2 : ℝ) * (2 * a)⁻¹) *
          (x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2)))) (Set.Ioi (1 : ℝ)) :=
        hbase_int.const_mul _
      refine h.congr_fun ?_ measurableSet_Ioi
      intro x _
      show -((2 * m + 2 : ℝ) * (2 * a)⁻¹) * (x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2))) =
        ((2 * m + 2 : ℝ) * x ^ (2 * m + 1)) * (-(2 * a)⁻¹ * Real.exp (-(a * x ^ 2)))
      ring
    have hzero : Tendsto ((fun y : ℝ => y ^ (2 * m + 2)) *
        (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (nhds ((1 : ℝ) ^ (2 * m + 2) * (-(2 * a)⁻¹ * Real.exp (-(a * 1 ^ 2))))) := by
      have hcont : Continuous ((fun y : ℝ => y ^ (2 * m + 2)) *
          (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))) := by fun_prop
      exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    have hinft : Tendsto ((fun y : ℝ => y ^ (2 * m + 2)) *
        (fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))) atTop (nhds 0) := by
      have h := (htend_pow (2 * m + 2)).const_mul (-(2 * a)⁻¹)
      have h2 : Tendsto (fun x : ℝ => -(2 * a)⁻¹ * (x ^ (2 * m + 2) * Real.exp (-(a * x ^ 2))))
          atTop (nhds 0) := by
        simpa using h
      refine h2.congr' ?_
      filter_upwards with x
      simp only [Pi.mul_apply]
      ring
    have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := (1 : ℝ))
      (u := fun y : ℝ => y ^ (2 * m + 2))
      (v := fun y : ℝ => -(2 * a)⁻¹ * Real.exp (-(a * y ^ 2)))
      (u' := fun y : ℝ => (2 * m + 2 : ℝ) * y ^ (2 * m + 1))
      (v' := fun y : ℝ => y * Real.exp (-(a * y ^ 2)))
      (a' := (1 : ℝ) ^ (2 * m + 2) * (-(2 * a)⁻¹ * Real.exp (-(a * 1 ^ 2)))) (b' := 0)
      hderiv_u hderiv_v' huv' hu'v hzero hinft
    have hIv : ∫ x in Set.Ioi (1 : ℝ),
        ((2 * m + 2 : ℝ) * x ^ (2 * m + 1)) * (-(2 * a)⁻¹ * Real.exp (-(a * x ^ 2)))
        = -((2 * m + 2 : ℝ) * (2 * a)⁻¹) * I m := by
      rw [show (fun x : ℝ => ((2 * m + 2 : ℝ) * x ^ (2 * m + 1)) *
            (-(2 * a)⁻¹ * Real.exp (-(a * x ^ 2))))
          = fun x => -((2 * m + 2 : ℝ) * (2 * a)⁻¹) *
              (x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2))) from by
        funext x
        ring]
      rw [integral_const_mul]
    rw [hI_succ, key, hIv]
    norm_num
    field_simp
  have hbase_closed : I 0 = Real.exp (-a) / (2 * a ^ (0 + 1)) *
      ∑ j ∈ Finset.range (0 + 1), ((Nat.factorial 0 : ℝ) / (j.factorial : ℝ)) * a ^ j := by
    rw [hbase]
    norm_num
  have hclosed : ∀ m : ℕ, I m = Real.exp (-a) / (2 * a ^ (m + 1)) *
      ∑ j ∈ Finset.range (m + 1), ((m.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j := by
    intro n
    induction n with
    | zero => exact hbase_closed
    | succ n ih =>
      rw [hrec n, ih]
      have hsum_succ : ∑ j ∈ Finset.range (n + 1 + 1),
          (((n + 1).factorial : ℝ) / (j.factorial : ℝ)) * a ^ j =
          (n + 1 : ℝ) * (∑ j ∈ Finset.range (n + 1),
            ((n.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j) + a ^ (n + 1) := by
        rw [Finset.sum_range_succ]
        have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hterm : ∑ j ∈ Finset.range (n + 1),
            (((n + 1).factorial : ℝ) / (j.factorial : ℝ)) * a ^ j =
            (n + 1 : ℝ) * ∑ j ∈ Finset.range (n + 1),
              ((n.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [hfac]
          field_simp
        have hlast : ((n + 1).factorial : ℝ) / ((n + 1).factorial : ℝ) * a ^ (n + 1) =
            a ^ (n + 1) := by
          field_simp
        rw [hterm, hlast]
      rw [hsum_succ]
      rw [show a ^ (n + 1 + 1) = a ^ (n + 1) * a by rw [pow_succ]]
      field_simp
      ring
  have hbound : 3 ≤ a → I m ≤ (m.factorial : ℝ) * Real.exp (-a) / 2 := by
    intro ha3
    have ha1 : (1 : ℝ) ≤ a := by linarith
    have hS_le : (∑ j ∈ Finset.range (m + 1), a ^ j / (j.factorial : ℝ)) ≤ a ^ (m + 1) := by
      have h1 : ∀ j ∈ Finset.range (m + 1), a ^ j / (j.factorial : ℝ) ≤
          a ^ m * (1 / (j.factorial : ℝ)) := by
        intro j hj
        have hjm : j ≤ m := by
          rw [Finset.mem_range] at hj
          omega
        have hje : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
        calc a ^ j / (j.factorial : ℝ) ≤ a ^ m / (j.factorial : ℝ) := by
              apply div_le_div_of_nonneg_right _ hje.le
              exact pow_le_pow_right₀ ha1 hjm
          _ = a ^ m * (1 / (j.factorial : ℝ)) := by ring
      calc (∑ j ∈ Finset.range (m + 1), a ^ j / (j.factorial : ℝ))
          ≤ ∑ j ∈ Finset.range (m + 1), a ^ m * (1 / (j.factorial : ℝ)) := Finset.sum_le_sum h1
        _ = a ^ m * ∑ j ∈ Finset.range (m + 1), 1 / (j.factorial : ℝ) := by rw [Finset.mul_sum]
        _ ≤ a ^ m * Real.exp 1 := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha.le m)
            simpa using Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (m + 1)
        _ ≤ a ^ m * a := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha.le m)
            linarith [Real.exp_one_lt_d9]
        _ = a ^ (m + 1) := by rw [pow_succ]
    have hS_le' : (∑ j ∈ Finset.range (m + 1),
        ((m.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j) ≤ (m.factorial : ℝ) * a ^ (m + 1) := by
      have hfac : (∑ j ∈ Finset.range (m + 1),
          ((m.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j) =
          (m.factorial : ℝ) * ∑ j ∈ Finset.range (m + 1), a ^ j / (j.factorial : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp
      rw [hfac]
      exact mul_le_mul_of_nonneg_left hS_le (by positivity)
    rw [hclosed m]
    calc Real.exp (-a) / (2 * a ^ (m + 1)) *
          ∑ j ∈ Finset.range (m + 1), ((m.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j
        ≤ Real.exp (-a) / (2 * a ^ (m + 1)) * ((m.factorial : ℝ) * a ^ (m + 1)) := by
          apply mul_le_mul_of_nonneg_left hS_le'
          positivity
      _ = (m.factorial : ℝ) * Real.exp (-a) / 2 := by
          field_simp
  exact ⟨hclosed m, hbound⟩
