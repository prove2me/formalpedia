-- Prove2me | solution 1 for DimCallCenters.Constraint.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:11:24.316142+00:00
-- url     : https://prove2.me/submissions/17d67e4e-5a01-4cd4-a218-6f339668960d

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_delayFn

set_option autoImplicit false
open DimCallCenters.Rationalized Set MeasureTheory

lemma dcc_pdf_cont : Continuous stdPdf := by
  unfold stdPdf; fun_prop

lemma dcc_pdf_pos (x : ℝ) : 0 < stdPdf x := by
  unfold stdPdf; positivity

lemma dcc_pdf_neg (x : ℝ) : stdPdf (-x) = stdPdf x := by
  simp [stdPdf]

lemma dcc_pdf_le (x : ℝ) : stdPdf x ≤ stdPdf 0 := by
  unfold stdPdf
  have : Real.exp (-x ^ 2 / 2) ≤ Real.exp (-(0:ℝ) ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    have := sq_nonneg x
    norm_num
    linarith
  exact mul_le_mul_of_nonneg_left this (by positivity)

lemma dcc_pdf_deriv (x : ℝ) : HasDerivAt stdPdf (-x * stdPdf x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    refine this.congr_deriv ?_
    norm_num; ring
  have h2 := (h1.exp).const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  unfold stdPdf
  refine h2.congr_deriv ?_
  ring

lemma dcc_pdf_integrable : Integrable stdPdf := by
  have h := (integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [stdPdf]
  congr 2
  ring

lemma dcc_pdf_total : ∫ x, stdPdf x = 1 := by
  have : ∫ x, stdPdf x = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, Real.exp (-(1/2 : ℝ) * x ^ 2) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [stdPdf]
    congr 2
    ring
  rw [this, integral_gaussian]
  have : Real.pi / (1/2 : ℝ) = 2 * Real.pi := by ring
  rw [this]
  have : 0 < Real.sqrt (2 * Real.pi) := by positivity
  field_simp

lemma dcc_cdf_zero : stdCdf 0 = 1 / 2 := by
  have hI : IntegrableOn stdPdf (Iic 0) := dcc_pdf_integrable.integrableOn
  have hJ : IntegrableOn stdPdf (Ioi 0) := dcc_pdf_integrable.integrableOn
  have h1 : (∫ x in Iic (0:ℝ), stdPdf x) + ∫ x in Ioi (0:ℝ), stdPdf x = 1 := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hI hJ, Iic_union_Ioi,
      setIntegral_univ]
    exact dcc_pdf_total
  have h2 : (∫ x in Iic (0:ℝ), stdPdf x) = ∫ x in Ioi (0:ℝ), stdPdf x := by
    have := integral_comp_neg_Iic (0:ℝ) stdPdf
    simp only [dcc_pdf_neg, neg_zero] at this
    exact this
  unfold stdCdf
  linarith

lemma dcc_cdf_eq (x : ℝ) : stdCdf x = stdCdf 0 + ∫ t in (0:ℝ)..x, stdPdf t := by
  have := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := x) (f := stdPdf) (μ := volume)
    dcc_pdf_integrable.integrableOn dcc_pdf_integrable.integrableOn
  unfold stdCdf
  linarith

lemma dcc_cdf_deriv (x : ℝ) : HasDerivAt stdCdf (stdPdf x) x := by
  have h := (Continuous.integral_hasStrictDerivAt dcc_pdf_cont 0 x).hasDerivAt.const_add (stdCdf 0)
  have : stdCdf = fun u => stdCdf 0 + ∫ t in (0:ℝ)..u, stdPdf t := funext dcc_cdf_eq
  rw [this]
  exact h

noncomputable def dccR (x : ℝ) : ℝ := 1 - stdCdf (-x)

lemma dccR_deriv (x : ℝ) : HasDerivAt dccR (stdPdf x) x := by
  have h := (dcc_cdf_deriv (-x)).comp x (hasDerivAt_neg x)
  have h2 := h.const_sub 1
  unfold dccR
  refine h2.congr_deriv ?_
  simp [dcc_pdf_neg]

lemma dccR_ge (x : ℝ) (hx : 0 ≤ x) : 1 / 2 ≤ dccR x := by
  have hmono : stdCdf (-x) ≤ stdCdf 0 := by
    have : Monotone stdCdf := by
      intro a b hab
      unfold stdCdf
      exact setIntegral_mono_set dcc_pdf_integrable.integrableOn
        (Filter.Eventually.of_forall (fun y => (dcc_pdf_pos y).le))
        (Filter.Eventually.of_forall (Iic_subset_Iic.mpr hab))
    exact this (by linarith)
  unfold dccR
  rw [dcc_cdf_zero] at hmono
  linarith

noncomputable def dccr (x : ℝ) : ℝ := dccR x / stdPdf x

lemma dccr_deriv (x : ℝ) : HasDerivAt dccr (1 + x * dccr x) x := by
  have h := (dccR_deriv x).div (dcc_pdf_deriv x) (dcc_pdf_pos x).ne'
  unfold dccr
  refine h.congr_deriv ?_
  have := (dcc_pdf_pos x).ne'
  field_simp
  ring

lemma dccr_ge (x : ℝ) (hx : 0 ≤ x) : 5 / 4 ≤ dccr x := by
  unfold dccr
  have h0 : stdPdf 0 ≤ 2 / 5 := by
    unfold stdPdf
    simp only [neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      Real.exp_zero, mul_one]
    have : (5 / 2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.pi_gt_d2]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hp := dcc_pdf_pos x
  have hle := dcc_pdf_le x
  have hR := dccR_ge x hx
  rw [le_div_iff₀ hp]
  nlinarith

lemma dcc_delay_eq (x : ℝ) : delayFn x = 1 / (1 + x * dccr x) := by
  unfold delayFn hazard dccr dccR
  rw [dcc_pdf_neg, div_div_eq_mul_div, mul_div_assoc]

theorem solution :
    StrictConvexOn ℝ (Set.Ioi 0) DimCallCenters.Rationalized.delayFn ∧
      StrictAntiOn DimCallCenters.Rationalized.delayFn (Set.Ioi 0) := by
  have hP : delayFn = fun x => 1 / (1 + x * dccr x) := funext dcc_delay_eq
  -- positivity of 1 + x r
  have hpos : ∀ x : ℝ, 0 ≤ x → 0 < 1 + x * dccr x := by
    intro x hx
    have := dccr_ge x hx
    have : 0 ≤ x * dccr x := mul_nonneg hx (by linarith)
    linarith
  -- first derivative on x > 0
  have hd1 : ∀ x : ℝ, 0 < x → HasDerivAt delayFn
      (-(((1 + x ^ 2) * dccr x + x)) / (1 + x * dccr x) ^ 2) x := by
    intro x hx
    have hw : HasDerivAt (fun y => 1 + y * dccr y) (x * (1 + x * dccr x) + dccr x) x := by
      have := (hasDerivAt_id x).mul (dccr_deriv x)
      have := this.const_add 1
      refine this.congr_deriv ?_
      simp only [id]; ring
    have := (hasDerivAt_const x (1:ℝ)).div hw (hpos x hx.le).ne'
    rw [hP]
    refine this.congr_deriv ?_
    have := (hpos x hx.le).ne'
    field_simp
    ring
  have hcont : ContinuousOn delayFn (Ioi 0) := by
    intro x hx
    have := hd1 x hx
    exact this.continuousAt.continuousWithinAt
  constructor
  · apply strictConvexOn_of_deriv2_pos (convex_Ioi 0) hcont
    intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have hev : deriv delayFn =ᶠ[nhds x]
        (fun y => -(((1 + y ^ 2) * dccr y + y)) / (1 + y * dccr y) ^ 2) := by
      filter_upwards [Ioi_mem_nhds hx0] with y hy
      exact (hd1 y hy).deriv
    have hd2 : HasDerivAt (fun y => -(((1 + y ^ 2) * dccr y + y)) / (1 + y * dccr y) ^ 2)
        ((((dccr x ^ 2) * (x ^ 4 + x ^ 2 + 2) + dccr x * x * (2 * x ^ 2 - 1) + (x ^ 2 - 2)))
          / (1 + x * dccr x) ^ 3) x := by
      have hu : HasDerivAt (fun y => (1 + y ^ 2) * dccr y + y)
          (2 * x * dccr x + (1 + x ^ 2) * (1 + x * dccr x) + 1) x := by
        have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
          have := (hasDerivAt_pow 2 x).const_add 1
          refine this.congr_deriv ?_
          simp
        have := (h1.mul (dccr_deriv x)).add (hasDerivAt_id x)
        refine this.congr_deriv ?_
        simp
      have hv : HasDerivAt (fun y => (1 + y * dccr y) ^ 2)
          (2 * (1 + x * dccr x) * (x * (1 + x * dccr x) + dccr x)) x := by
        have hw : HasDerivAt (fun y => 1 + y * dccr y) (x * (1 + x * dccr x) + dccr x) x := by
          have := (hasDerivAt_id x).mul (dccr_deriv x)
          have := this.const_add 1
          refine this.congr_deriv ?_
          simp only [id]; ring
        have := hw.pow 2
        refine this.congr_deriv ?_
        simp
      have := (hu.neg).div hv (pow_pos (hpos x hx0.le) 2).ne'
      refine this.congr_deriv ?_
      have := (hpos x hx0.le).ne'
      simp only [Pi.neg_apply]
      field_simp
      ring
    have hderiv2 : deriv (deriv delayFn) x = (((dccr x ^ 2) * (x ^ 4 + x ^ 2 + 2) + dccr x * x * (2 * x ^ 2 - 1) + (x ^ 2 - 2))
          / (1 + x * dccr x) ^ 3) := by
      rw [hev.deriv_eq]
      exact hd2.deriv
    show 0 < deriv (deriv delayFn) x
    rw [hderiv2]
    have hr := dccr_ge x hx0.le
    have hq : 0 < (dccr x ^ 2) * (x ^ 4 + x ^ 2 + 2) + dccr x * x * (2 * x ^ 2 - 1) + (x ^ 2 - 2) := by
      set s := dccr x - 5 / 4 with hs
      have hs0 : 0 ≤ s := by linarith
      have e : dccr x = s + 5 / 4 := by linarith
      rw [e]
      have a1 : 0 < x ^ 4 + x ^ 2 + 2 := by positivity
      have a2 : 0 < 5 / 2 * x ^ 4 + 2 * x ^ 3 + 5 / 2 * x ^ 2 - x + 5 := by
        nlinarith [sq_nonneg (x - 1/5), sq_nonneg (x ^ 2), sq_nonneg x, pow_pos hx0 3]
      have a3 : 0 < 25 / 16 * x ^ 4 + 5 / 2 * x ^ 3 + 41 / 16 * x ^ 2 - 5 / 4 * x + 9 / 8 := by
        nlinarith [sq_nonneg (x - 1/2), sq_nonneg (x ^ 2), sq_nonneg x, pow_pos hx0 3]
      have key : (s + 5 / 4) ^ 2 * (x ^ 4 + x ^ 2 + 2) + (s + 5 / 4) * x * (2 * x ^ 2 - 1) + (x ^ 2 - 2)
          = (x ^ 4 + x ^ 2 + 2) * s ^ 2 + (5 / 2 * x ^ 4 + 2 * x ^ 3 + 5 / 2 * x ^ 2 - x + 5) * s
            + (25 / 16 * x ^ 4 + 5 / 2 * x ^ 3 + 41 / 16 * x ^ 2 - 5 / 4 * x + 9 / 8) := by ring
      rw [key]
      have := mul_nonneg a1.le (sq_nonneg s)
      have := mul_nonneg a2.le hs0
      linarith
    exact div_pos hq (pow_pos (hpos x hx0.le) 3)
  · apply strictAntiOn_of_deriv_neg (convex_Ioi 0) hcont
    intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    rw [(hd1 x hx0).deriv]
    have hr := dccr_ge x hx0.le
    have : 0 < (1 + x ^ 2) * dccr x + x := by
      have : 0 < dccr x := by linarith
      positivity
    have h2 := pow_pos (hpos x hx0.le) 2
    exact div_neg_of_neg_of_pos (by linarith) h2
