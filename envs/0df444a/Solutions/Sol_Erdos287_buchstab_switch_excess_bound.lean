-- Prove2me | solution 1 for Erdos287.buchstab_switch_excess_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T18:37:54.035017+00:00
-- url     : https://prove2.me/submissions/f910fa16-dfd1-4dfa-9db8-f12f29fa635d

import Mathlib

open Set MeasureTheory

set_option autoImplicit false

private theorem triangle_integral (d b : ℝ) :
    (∫ v in d..b, (v - d) * (b - v)) = (b - d) ^ 3 / 6 := by
  have hcont : Continuous (fun v : ℝ => (v - d) * (b - v)) := by fun_prop
  let primitive (v : ℝ) := (b - d) * (v - d) ^ 2 / 2 - (v - d) ^ 3 / 3
  have hderiv (v : ℝ) : HasDerivAt primitive ((v - d) * (b - v)) v := by
    have hv : HasDerivAt (fun x : ℝ => x - d) 1 v := (hasDerivAt_id v).sub_const d
    unfold primitive
    convert! (((hv.pow 2).const_mul (b - d)).div_const 2).sub ((hv.pow 3).div_const 3) using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hderiv v)
    (hcont.intervalIntegrable d b)]
  simp [primitive]
  ring

/-- Bound the one-dimensional excess in the switched Chen integral after
integrating the two outside prime exponents. -/
theorem solution (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (hb : b < 1 / 3)
    (had : a ≤ (1 - b) / (2 + 1 / c)) (hdb : (1 - b) / (2 + 1 / c) ≤ b) :
    let d := (1 - b) / (2 + 1 / c)
    2 * (∫ v in a..b, max 0 (v / (1 - 2 * v - b) - c) *
        (Real.log (v / a) * Real.log (b / v) / v ^ 2)) ≤
      (1 + 2 * c) * Real.log (b / a) * (b - d) ^ 3 / (3 * (1 - 3 * b) * d ^ 3) := by
  dsimp only
  let d := (1 - b) / (2 + 1 / c)
  let f (v : ℝ) := max 0 (v / (1 - 2 * v - b) - c) *
    (Real.log (v / a) * Real.log (b / v) / v ^ 2)
  change 2 * (∫ v in a..b, f v) ≤
    (1 + 2 * c) * Real.log (b / a) * (b - d) ^ 3 / (3 * (1 - 3 * b) * d ^ 3)
  have hab : a ≤ b := had.trans hdb
  have hd : 0 < d := ha.trans_le had
  have hbpos : 0 < b := hd.trans_le hdb
  have hbot : 0 < 1 - 3 * b := by linarith
  have hden (v : ℝ) (hv : v ≤ b) : 0 < 1 - 2 * v - b := by linarith
  have hd_eq : (1 + 2 * c) * d = c * (1 - b) := by
    dsimp only [d]
    have h : 0 < 2 + 1 / c := by positivity
    field_simp
    ring
  have hrewrite (v : ℝ) (hv : v ≤ b) :
      v / (1 - 2 * v - b) - c = (1 + 2 * c) * (v - d) / (1 - 2 * v - b) := by
    apply (eq_div_iff (hden v hv).ne').2
    rw [sub_mul, div_mul_cancel₀ _ (hden v hv).ne']
    linear_combination hd_eq
  have hcont : ContinuousOn f (Icc a b) := by
    have hv : ∀ v ∈ Icc a b, 0 < v := fun _ hv => ha.trans_le hv.1
    have hratio : ContinuousOn (fun v : ℝ => v / (1 - 2 * v - b)) (Icc a b) :=
      continuous_id.continuousOn.div (by fun_prop) (fun v hv => (hden v hv.2).ne')
    have hloga : ContinuousOn (fun v : ℝ => Real.log (v / a)) (Icc a b) :=
      (continuous_id.div_const a).continuousOn.log (fun v hx => (div_pos (hv v hx) ha).ne')
    have hlogb : ContinuousOn (fun v : ℝ => Real.log (b / v)) (Icc a b) :=
      (continuousOn_const.div continuous_id.continuousOn (fun v hx => (hv v hx).ne')).log
        (fun v hx => (div_pos hbpos (hv v hx)).ne')
    exact (ContinuousOn.sup continuousOn_const (hratio.sub continuousOn_const)).mul
      ((hloga.mul hlogb).div (by fun_prop) (fun v hx => pow_ne_zero _ (hv v hx).ne'))
  have hleft : IntervalIntegrable f volume a d :=
    (hcont.mono (Icc_subset_Icc_right hdb)).intervalIntegrable_of_Icc had
  have hright : IntervalIntegrable f volume d b :=
    (hcont.mono (Icc_subset_Icc_left had)).intervalIntegrable_of_Icc hdb
  have hzero : (∫ v in a..d, f v) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) ?_, intervalIntegral.integral_zero]
    intro v hv
    rw [uIcc_of_le had] at hv
    dsimp only [f]
    rw [hrewrite v (hv.2.trans hdb), max_eq_left, zero_mul]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hv.2))
      (hden v (hv.2.trans hdb)).le
  let C := (1 + 2 * c) * Real.log (b / a) / ((1 - 3 * b) * d ^ 3)
  have hmajor (v : ℝ) (hv : v ∈ Icc d b) : f v ≤ C * ((v - d) * (b - v)) := by
    have hvpos := hd.trans_le hv.1
    have hav := had.trans hv.1
    have hla := Real.log_nonneg ((le_div_iff₀ ha).2 (by simpa using hav))
    have hlb := Real.log_nonneg ((le_div_iff₀ hvpos).2 (by simpa using hv.2))
    have hdiff : 0 ≤ v - d := sub_nonneg.mpr hv.1
    have hrem : 0 ≤ b - v := sub_nonneg.mpr hv.2
    have hnum : 0 ≤ (1 + 2 * c) * (v - d) := mul_nonneg (by positivity) hdiff
    have h₁ : max 0 (v / (1 - 2 * v - b) - c) ≤ (1 + 2 * c) * (v - d) / (1 - 3 * b) := by
      rw [hrewrite v hv.2, max_eq_right (div_nonneg hnum (hden v hv.2).le)]
      exact div_le_div_of_nonneg_left hnum hbot (by linarith [hv.2])
    have h₂ : Real.log (v / a) ≤ Real.log (b / a) :=
      Real.log_le_log (div_pos hvpos ha) (div_le_div_of_nonneg_right hv.2 ha.le)
    have h₃ : Real.log (b / v) ≤ (b - v) / d := by
      calc
        Real.log (b / v) ≤ b / v - 1 := Real.log_le_sub_one_of_pos (div_pos hbpos hvpos)
        _ = (b - v) / v := by field_simp
        _ ≤ (b - v) / d := div_le_div_of_nonneg_left hrem hd hv.1
    have hquot : Real.log (v / a) * Real.log (b / v) / v ^ 2 ≤
        Real.log (b / a) * ((b - v) / d) / d ^ 2 := by
      have hproduct := mul_le_mul h₂ h₃ hlb (hla.trans h₂)
      exact (div_le_div_of_nonneg_right hproduct (sq_nonneg v)).trans
        (div_le_div_of_nonneg_left (mul_nonneg (hla.trans h₂) (div_nonneg hrem hd.le)) (by positivity)
          (pow_le_pow_left₀ hd.le hv.1 2))
    have hflog : 0 ≤ Real.log (v / a) * Real.log (b / v) / v ^ 2 := by positivity
    calc
      f v ≤ ((1 + 2 * c) * (v - d) / (1 - 3 * b)) *
          (Real.log (b / a) * ((b - v) / d) / d ^ 2) :=
        mul_le_mul h₁ hquot hflog (by positivity)
      _ = C * ((v - d) * (b - v)) := by
        dsimp [C]
        field_simp
  have hpoly : Continuous (fun v : ℝ => C * ((v - d) * (b - v))) := by fun_prop
  have hmain := intervalIntegral.integral_mono_on hdb hright (hpoly.intervalIntegrable d b) hmajor
  rw [intervalIntegral.integral_const_mul, triangle_integral] at hmain
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hzero, zero_add]
  calc
    2 * (∫ v in d..b, f v) ≤ 2 * (C * ((b - d) ^ 3 / 6)) := by linarith
    _ = _ := by
      dsimp [C]
      field_simp
      ring

