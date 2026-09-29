-- Prove2me | solution 1 for ErlerGross.integral_cosh_div_cosh_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T18:24:42.688026+00:00
-- url     : https://prove2.me/submissions/68098a14-3d84-4046-8b3f-adce0ed415d6

import Mathlib

open Real MeasureTheory Set

private lemma cosh_norm_upper (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.cosh]
  calc
    ‖(Complex.exp z + Complex.exp (-z)) / 2‖ ≤
        (Real.exp z.re + Real.exp (-z.re)) / 2 := by
      rw [Complex.norm_div]
      simp only [Complex.norm_ofNat]
      calc
        ‖Complex.exp z + Complex.exp (-z)‖ / 2 ≤
            (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 := by
          exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
        _ = (Real.exp z.re + Real.exp (-z.re)) / 2 := by
          simp [Complex.norm_exp]
    _ = Real.cosh z.re := by rw [Real.cosh_eq]
    _ ≤ Real.exp |z.re| := by
      rw [Real.cosh_eq]
      have h1 : Real.exp z.re ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (le_abs_self _)
      have h2 : Real.exp (-z.re) ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (neg_le_abs _)
      linarith

private lemma cosh_norm_lower (z : ℂ) :
    Real.exp z.re - Real.exp (-z.re) ≤ 2 * ‖Complex.cosh z‖ := by
  rw [Complex.cosh]
  have h := norm_sub_norm_le (Complex.exp z) (-Complex.exp (-z))
  have h' : Real.exp z.re - Real.exp (-z.re) ≤
      ‖Complex.exp z + Complex.exp (-z)‖ := by
    simpa [Complex.norm_exp, norm_neg, sub_eq_add_neg] using h
  rw [Complex.norm_div]
  norm_num
  nlinarith [h']

private lemma cosh_ratio_bound (a b : ℂ) (hab : |a.re| < b.re) {x : ℝ} (hx : 1 < x) :
    ‖Complex.cosh (a * x) / Complex.cosh (b * x)‖ ≤
      (2 / (1 - Real.exp (-2 * b.re))) * Real.exp (-(b.re - |a.re|) * x) := by
  have hb : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hab
  have hd : 0 < b.re - |a.re| := sub_pos.mpr hab
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx.le
  have hu : b.re ≤ b.re * x := by nlinarith [mul_nonneg hb.le hx0]
  have hnum : ‖Complex.cosh (a * x)‖ ≤ Real.exp (|a.re| * x) := by
    have hh := cosh_norm_upper (a * x)
    simpa [Complex.mul_re, abs_of_nonneg hx0] using hh
  let c : ℝ := 1 - Real.exp (-2 * b.re)
  have hc : 0 < c := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hu' : b.re * x ≤ b.re * x := le_rfl
  have hexpmono : Real.exp (-2 * (b.re * x)) ≤ Real.exp (-2 * b.re) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdiff : c * Real.exp (b.re * x) ≤
      Real.exp (b.re * x) - Real.exp (-(b.re * x)) := by
    have he : Real.exp (-(b.re * x)) = Real.exp (b.re * x) * Real.exp (-2 * (b.re * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    dsimp [c]
    nlinarith [mul_nonneg (Real.exp_pos (b.re * x)).le
      (sub_nonneg.mpr hexpmono)]
  have hden0 : 0 < ‖Complex.cosh (b * x)‖ := by
    have hlow := cosh_norm_lower (b * x)
    have hre : (b * x).re = b.re * x := by simp
    rw [hre] at hlow
    have hpos : 0 < Real.exp (b.re * x) - Real.exp (-(b.re * x)) := by
      have : Real.exp (-(b.re * x)) < Real.exp (b.re * x) :=
        Real.exp_lt_exp.mpr (by nlinarith [hu])
      linarith
    linarith
  have hden : c * Real.exp (b.re * x) ≤ 2 * ‖Complex.cosh (b * x)‖ := by
    have hlow := cosh_norm_lower (b * x)
    have hre : (b * x).re = b.re * x := by simp
    rw [hre] at hlow
    linarith [hdiff]
  have hfactor :
      Real.exp (|a.re| * x) ≤
        ‖Complex.cosh (b * x)‖ * (2 / c * Real.exp (-(b.re - |a.re|) * x)) := by
    have hmul := mul_le_mul_of_nonneg_right hden
      (mul_nonneg (by positivity : 0 ≤ 1 / c)
        (Real.exp_pos (-(b.re - |a.re|) * x)).le)
    have heq : (c * Real.exp (b.re * x)) * (1 / c *
        Real.exp (-(b.re - |a.re|) * x)) = Real.exp (|a.re| * x) := by
      have hcne : c ≠ 0 := ne_of_gt hc
      field_simp
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hmul
    calc
      Real.exp (|a.re| * x) ≤
          2 * ‖Complex.cosh (b * x)‖ *
            (1 / c * Real.exp (-(b.re - |a.re|) * x)) := hmul
      _ = ‖Complex.cosh (b * x)‖ *
            (2 / c * Real.exp (-(b.re - |a.re|) * x)) := by ring
  rw [Complex.norm_div]
  have hquot' : ‖Complex.cosh (a * x)‖ / ‖Complex.cosh (b * x)‖ ≤
      (2 / c) * Real.exp (-(b.re - |a.re|) * x) := by
    apply (div_le_iff₀ hden0).2
    calc
      ‖Complex.cosh (a * x)‖ ≤ Real.exp (|a.re| * x) := hnum
      _ ≤ ‖Complex.cosh (b * x)‖ *
          (2 / c * Real.exp (-(b.re - |a.re|) * x)) := hfactor
      _ = (2 / c * Real.exp (-(b.re - |a.re|) * x)) *
          ‖Complex.cosh (b * x)‖ := by ring
  simpa [c, mul_assoc] using hquot'

theorem solution (a b : ℂ) (hab : |a.re| < b.re) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x)) (Set.Ioi 1) := by
  let f : ℝ → ℂ := fun x => Complex.cosh (a * x) / Complex.cosh (b * x)
  let δ : ℝ := b.re - |a.re|
  let c : ℝ := 1 - Real.exp (-2 * b.re)
  have hδ : 0 < δ := by dsimp [δ]; exact sub_pos.mpr hab
  have hc : 0 < c := by
    dsimp [c]
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    linarith [lt_of_le_of_lt (abs_nonneg a.re) hab]
  have hg : IntegrableOn (fun x : ℝ => (2 / c) * Real.exp (-δ * x)) (Set.Ioi 1) := by
    have hexp : IntegrableOn (fun x : ℝ => Real.exp (-δ * x)) (Set.Ioi 1) :=
      integrableOn_exp_mul_Ioi (by nlinarith) 1
    change Integrable (fun x : ℝ => (2 / c) * Real.exp (-δ * x))
      (volume.restrict (Set.Ioi 1))
    simpa only [smul_eq_mul] using hexp.const_mul (2 / c)
  change Integrable f (volume.restrict (Set.Ioi 1))
  apply Integrable.mono' hg
  · have hfc : ContinuousOn f (Set.Ioi 1) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx
      have hlow := cosh_norm_lower (b * x)
      have hre : (b * x).re = b.re * x := by simp
      rw [hre] at hlow
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      have hb : 0 < b.re := lt_of_le_of_lt (abs_nonneg a.re) hab
      have hu : 0 < b.re * x := mul_pos hb hx0
      have hpos : 0 < Real.exp (b.re * x) - Real.exp (-(b.re * x)) := by
        have he := Real.exp_lt_exp.mpr (lt_of_le_of_lt (neg_nonpos.mpr hu.le) hu)
        linarith
      have hn : 0 < ‖Complex.cosh (b * x)‖ := by nlinarith [hlow]
      intro hz
      rw [hz] at hn
      norm_num at hn
    exact ContinuousOn.aestronglyMeasurable hfc measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa [f, c, δ, mul_assoc, mul_left_comm, mul_comm] using
      cosh_ratio_bound a b hab hx
