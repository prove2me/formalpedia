-- Prove2me | solution 1 for GRH.smoothed_mobius_nine_tenths_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:27:52.395834+00:00
-- url     : https://prove2.me/submissions/89758ed1-698a-4b03-a705-cc7dc47e3244

import Theorems.Thm_OAI_VerticalContourShift_exp_mellin_bound_of_polynomial_multiplier
import Theorems.Thm_GRH_reciprocal_nonprincipal_nine_tenths
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Mathlib.Analysis.MellinInversion
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_mellin_identity
import Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_continuousOn_pos
import Theorems.Thm_Helfgott_LFunction_contour_growth_inputs

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Complex Set MeasureTheory

private theorem gamma_integral_bound (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx _]
  simp

private theorem gamma_shift_norm (a : ℝ) (ha : 0 < a) (m : ℕ) (z : ℂ) (hz : a ≤ z.re) :
    (1 + |z.im|) ^ m * ‖Complex.Gamma z‖ ≤
      (1 / a + 1) ^ m * ‖Complex.Gamma (z + m)‖ := by
  induction m generalizing z with
  | zero => simp
  | succ n ih =>
    have hza : a ≤ ‖z‖ := hz.trans (Complex.re_le_norm _)
    have hK : 0 ≤ 1 / a + 1 := by positivity
    have hfac : 1 + |z.im| ≤ (1 / a + 1) * ‖z‖ := by
      have hOne : 1 ≤ ‖z‖ / a := (one_le_div ha).mpr hza
      have hIm := Complex.abs_im_le_norm z
      rw [add_mul, one_div_mul_eq_div, one_mul]
      linarith
    have hz0 : z ≠ 0 := by
      intro h
      simpa [h] using (ha.trans_le hz)
    have hshift := ih (z + 1) (by simpa using (show a ≤ z.re + 1 by linarith))
    rw [pow_succ, pow_succ]
    calc
      (1 + |z.im|) ^ n * (1 + |z.im|) * ‖Complex.Gamma z‖ ≤
          (1 + |z.im|) ^ n * ((1/a + 1) * ‖z‖) * ‖Complex.Gamma z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by positivity)) (norm_nonneg _)
      _ = (1/a + 1) * ((1+|z.im|)^n * ‖Complex.Gamma (z+1)‖) := by
        rw [Complex.Gamma_add_one _ hz0, norm_mul]
        ring
      _ ≤ (1/a + 1) * ((1/a+1)^n * ‖Complex.Gamma (z+1 + n)‖) := by
        apply mul_le_mul_of_nonneg_left _ hK
        simpa using hshift
      _ = (1/a+1)^n * (1/a+1) * ‖Complex.Gamma (z + (↑(n+1) : ℂ))‖ := by
        rw [Nat.cast_add_one, add_assoc z, add_comm (1 : ℂ)]
        ring

private theorem gamma_rapid_decay_on_positive_strip (a b : ℝ) (ha : 0 < a) (_hab : a ≤ b) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖Complex.Gamma z‖ ≤ C / (1 + |z.im|) ^ m := by
  have hcont : ContinuousOn Real.Gamma (Icc (a + m) (b + m)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (by
      intro x hx
      exact (show 0 < a + (m : ℝ) by positivity).trans_le hx.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcont
  let K : ℝ := (1/a + 1)^m
  refine ⟨K * (|M|+1), by dsimp [K]; positivity, ?_⟩
  intro z hz hz'
  have hzm : (z+(m:ℂ)).re = z.re + (m : ℝ) := by simp
  have hpos : 0 < (z+(m:ℂ)).re := by rw [hzm]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hbound : ‖Complex.Gamma (z+m)‖ ≤ |M| + 1 := by
    apply (gamma_integral_bound _ hpos).trans
    have h := hM ⟨(z+(m:ℂ)).re, (by rw [hzm]; exact ⟨by linarith,by linarith⟩), rfl⟩
    linarith [le_abs_self M]
  apply (le_div_iff₀ (by positivity)).2
  rw [mul_comm]
  exact (gamma_shift_norm a ha m z hz).trans (mul_le_mul_of_nonneg_left hbound (by positivity))

private theorem integrable_gamma_two_vertical : Integrable (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, hbd⟩ := gamma_rapid_decay_on_positive_strip 2 2 (by norm_num) le_rfl 2
  let f : ℝ → ℂ := fun t => (2 : ℂ) + (t : ℂ) * Complex.I
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hre (t : ℝ) : (f t).re = 2 := by simp [f]
  have him (t : ℝ) : (f t).im = t := by simp [f]
  have hc : Continuous (fun t => Complex.Gamma (f t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    refine (Complex.continuousAt_Gamma (f t) ?_).comp (hf.continuousAt)
    intro n hn
    have heq := congrArg Complex.re hn
    rw [hre] at heq
    simp only [Complex.neg_re, Complex.natCast_re] at heq
    linarith [Nat.cast_nonneg (α := ℝ) n]
  apply ((integrable_inv_one_add_sq).const_mul C).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have h := hbd (f t) (hre t).ge (hre t).le
  rw [him] at h
  refine h.trans ?_
  change C / (1 + |t|)^2 ≤ C * (1 + t^2)⁻¹
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hC.le (by positivity)
  nlinarith [abs_nonneg t, sq_abs t]

open MeasureTheory Complex
open OAI.ShortDraftMellin

private theorem smoothed_inverse_mellin_two (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (D : ℝ) (hD : 0 < D) :
    mobiusExpSum χ D⁻¹ =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ,
        Complex.Gamma ((2:ℂ) + (t:ℂ) * Complex.I) *
        (D:ℂ) ^ ((2:ℂ) + (t:ℂ) * Complex.I) *
        (χ.LFunction ((2:ℂ) + (t:ℂ) * Complex.I))⁻¹ := by
  let z (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  have hre (t : ℝ) : (z t).re = 2 := by simp [z]
  have hz1 (t : ℝ) : z t ≠ 1 := by
    intro e
    have h := congrArg Complex.re e
    rw [hre] at h
    norm_num at h
  have hline (t : ℝ) : (1/2:ℝ) ≤ ‖χ.LFunction (z t)‖ :=
    (Helfgott.LFunction_contour_growth_inputs q χ 0 2).1 (z t) (hre t).ge
  have hL (t : ℝ) : χ.LFunction (z t) ≠ 0 := by
    intro e
    have h := hline t
    rw [e, norm_zero] at h
    norm_num at h
  have hM (s : ℂ) (hs : 1 < s.re) :
      χ.LFunction s * mellin (mobiusExpSum χ) s = Gamma s := by
    simpa only [mellin_comp_inv, neg_neg] using dirichlet_exp_mellin_identity χ s hs
  have hMf (t : ℝ) : mellin (mobiusExpSum χ) (z t) =
      Gamma (z t) * (χ.LFunction (z t))⁻¹ := by
    rw [← div_eq_mul_inv, eq_div_iff (hL t), mul_comm]
    exact hM (z t) (by rw [hre]; norm_num)
  have hconv : MellinConvergent (mobiusExpSum χ) (2:ℂ) := by
    by_contra h
    have he : mellin (mobiusExpSum χ) (2:ℂ) = 0 := integral_undef h
    have hg := hM 2 (by norm_num)
    rw [he, mul_zero] at hg
    exact (Gamma_ne_zero_of_re_pos (by norm_num : (0:ℝ) < (2:ℂ).re)) hg.symm
  have hcL : Continuous (fun t : ℝ => (χ.LFunction (z t))⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hzt : ContinuousAt z t := by dsimp [z]; fun_prop
    exact ((χ.differentiableAt_LFunction (z t) (Or.inl (hz1 t))).continuousAt.comp hzt).inv₀ (hL t)
  have hbound (t : ℝ) : ‖(χ.LFunction (z t))⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr (hL t))]
    linarith [hline t]
  have hG : Integrable (fun t : ℝ => Gamma (z t)) := integrable_gamma_two_vertical
  have hvertical : VerticalIntegrable (mellin (mobiusExpSum χ)) 2 := by
    change Integrable (fun t : ℝ => mellin (mobiusExpSum χ) (z t))
    exact (hG.mul_bdd hcL.aestronglyMeasurable (Filter.Eventually.of_forall hbound)).congr
      (Filter.Eventually.of_forall fun t => (hMf t).symm)
  have hcx : ContinuousAt (mobiusExpSum χ) D⁻¹ :=
    (mobiusExpSum_continuousOn_pos χ).continuousAt (IsOpen.mem_nhds isOpen_Ioi (inv_pos.mpr hD))
  calc
    _ = mellinInv 2 (mellin (mobiusExpSum χ)) D⁻¹ :=
      (mellinInv_mellin_eq 2 _ (inv_pos.mpr hD) (by simpa using hconv) hvertical hcx).symm
    _ = _ := by
      simp only [mellinInv, Complex.real_smul, one_div, Complex.ofReal_inv, Complex.ofReal_ofNat, smul_eq_mul]
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      change ((D:ℂ)⁻¹) ^ (-(z t)) * mellin (mobiusExpSum χ) (z t) = _
      rw [Complex.inv_cpow_ofReal_nonneg hD.le (-(z t)), Complex.cpow_neg, inv_inv]
      rw [hMf]
      dsimp only [z]
      ring

theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 1 ≤ D →
      ‖mobiusExpSum χ D⁻¹‖ ≤ C * D ^ (9 / 10 : ℝ) := by
  apply OAI.VerticalContourShift.exp_mellin_bound_of_polynomial_multiplier
    (9 / 10 : ℝ) 2 (by norm_num) (by norm_num)
    (fun s : ℂ => (χ.LFunction s)⁻¹)
    (fun D : ℝ => mobiusExpSum χ D⁻¹) (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  · intro s hs _
    exact (χ.differentiableAt_LFunction s (Or.inr hχ)).inv
      (TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ (by linarith) (fun h => hχ h.1))
  · exact GRH.reciprocal_nonprincipal_nine_tenths q χ hχ
  · exact gamma_rapid_decay_on_positive_strip _ _ (by norm_num) (by norm_num)
  · intro D hD
    exact smoothed_inverse_mellin_two q χ D (lt_of_lt_of_le zero_lt_one hD)
