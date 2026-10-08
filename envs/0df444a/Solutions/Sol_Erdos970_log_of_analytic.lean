-- Prove2me | solution 1 for Erdos970.log_of_analytic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:17:54.730747+00:00
-- url     : https://prove2.me/submissions/661b2357-6a95-422f-b25a-10c4d69eb6a1

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT1_ComplexAnalysis
namespace Erdos970






































lemma lem_wReIm (w : ℂ) : w = w.re + Complex.I * w.im := by
  apply Complex.ext
  simp
  simp































































































































































































open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Interval


lemma def_If_z_plus_h
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, f (( (z + h).re : ℂ) + Complex.I * τ)) := by
  rfl

lemma def_If_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) := by
  rfl

lemma def_If_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (_hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  simp [If_taxicab]

lemma continuous_vertical_line (a : ℂ) :
  Continuous (fun τ : ℝ => ((a.re : ℂ) + Complex.I * (τ : ℂ))) := by
  have hconst : Continuous (fun _ : ℝ => (a.re : ℂ)) := continuous_const
  have hmul : Continuous (fun τ : ℝ => (Complex.I : ℂ) * (τ : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  convert (preTransparency := .instances) hconst.add hmul using 1

lemma norm_re_add_I_mul_le_norm (a : ℂ) {τ : ℝ} (hτ : |τ| ≤ |a.im|) :
  ‖((a.re : ℂ) + Complex.I * (τ : ℂ))‖ ≤ ‖a‖ := by
                                                                              
  set z1 : ℂ := ((a.re : ℂ) + Complex.I * (τ : ℂ)) with hz1
                                       
  have hsq_z1 : ‖z1‖ ^ 2 = z1.re ^ 2 + z1.im ^ 2 := by
    have hx : ‖z1‖ ^ 2 - z1.re ^ 2 = z1.im ^ 2 := Complex.sq_norm_sub_sq_re z1
    have hx' := congrArg (fun t : ℝ => t + z1.re ^ 2) hx
                                          
    have : ‖z1‖ ^ 2 = z1.im ^ 2 + z1.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
  have hsq_a : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    have hx : ‖a‖ ^ 2 - a.re ^ 2 = a.im ^ 2 := Complex.sq_norm_sub_sq_re a
    have hx' := congrArg (fun t : ℝ => t + a.re ^ 2) hx
    have : ‖a‖ ^ 2 = a.im ^ 2 + a.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
                             
  have hz1_re : z1.re = a.re := by
    simp [hz1, mul_comm]
  have hz1_im : z1.im = τ := by
    simp [hz1, mul_comm]
                                                  
  have hτ_sq : τ ^ 2 ≤ a.im ^ 2 := by
    simpa using (sq_le_sq.mpr hτ)
                    
  have hsq_le : ‖z1‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have : a.re ^ 2 + τ ^ 2 ≤ a.re ^ 2 + a.im ^ 2 := add_le_add_right hτ_sq _
    simpa [hsq_z1, hz1_re, hz1_im, hsq_a] using this
                               
  have hnonneg : 0 ≤ ‖a‖ := norm_nonneg _
  exact le_of_sq_le_sq hsq_le hnonneg

lemma closedBall_mono_center0 {r1 R : ℝ} (h : r1 ≤ R) :
  Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
  intro z hz
  have hz' : dist z (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp hz)
  exact Metric.mem_closedBall.mpr (le_trans hz' h)

lemma abs_le_abs_of_mem_uIcc_zero {b t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) b) : |t| ≤ |b| := by
  classical
  by_cases hb : 0 ≤ b
  ·                                  
    have ht' : t ∈ Set.Icc (0 : ℝ) b := by
      simpa [Set.uIcc_of_le hb] using ht
    have ht0 : 0 ≤ t := ht'.1
    have htb : t ≤ b := ht'.2
    have htabs : |t| = t := abs_of_nonneg ht0
    have hbabs : |b| = b := abs_of_nonneg hb
    simpa [htabs, hbabs] using htb
  ·                                  
    have ht' : t ∈ Set.Icc b 0 := by
      simpa [Set.uIcc_of_not_le hb] using ht
    have hb_le : b ≤ 0 := le_trans ht'.1 ht'.2
    have ht_le0 : t ≤ 0 := ht'.2
    have hbabs : |b| = -b := abs_of_nonpos hb_le
    have htabs : |t| = -t := abs_of_nonpos ht_le0
    have hneg : -t ≤ -b := neg_le_neg ht'.1
    simpa [htabs, hbabs] using hneg

lemma vertical_intervalIntegrable_of_mem_ball
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {a : ℂ}
    (ha : a ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ : ℝ => f (((a.re : ℂ)) + Complex.I * τ)) volume (0 : ℝ) a.im := by
  classical
                                              
  have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
                                 
  let g : ℝ → ℂ := fun τ => ((a.re : ℂ) + Complex.I * (τ : ℂ))
                                                        
  have hg_cont : ContinuousOn g (Set.uIcc (0 : ℝ) a.im) := by
    simpa [g] using (continuous_vertical_line a).continuousOn
                                                                  
  have hg_maps : Set.MapsTo g (Set.uIcc (0 : ℝ) a.im) (Metric.closedBall (0 : ℂ) R) := by
    intro τ hτ
    have hτabs : |τ| ≤ |a.im| := abs_le_abs_of_mem_uIcc_zero hτ
    have hnorm_le_a : ‖g τ‖ ≤ ‖a‖ := by
      simpa [g] using norm_re_add_I_mul_le_norm a hτabs
    have ha_norm : ‖a‖ ≤ r1 := by
      have : dist a (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp ha)
      simpa [dist_eq_norm] using this
    have hnorm_le_r1 : ‖g τ‖ ≤ r1 := le_trans hnorm_le_a ha_norm
    have hg_mem_r1 : g τ ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le_r1
    exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) hg_mem_r1
                                                                          
  have hcomp : ContinuousOn (fun τ : ℝ => f (g τ)) (Set.uIcc (0 : ℝ) a.im) := by
                                                      
    convert (preTransparency := .instances) (ContinuousOn.comp (hg := hf_cont) (hf := hg_cont) (h := hg_maps)) using 1; rfl
                                                           
  have hInt : IntervalIntegrable (fun τ : ℝ => f (g τ)) volume (0 : ℝ) a.im :=
    ContinuousOn.intervalIntegrable (u := fun τ : ℝ => f (g τ)) (a := 0) (b := a.im) hcomp
  simpa [g] using hInt

lemma helper_im_of_w (z h : ℂ) : (((((z + h).re : ℂ) + Complex.I * z.im)).im) = z.im := by
  simp [Complex.add_im]

lemma helper_mul_sub_complex (x y : ℂ) : Complex.I * x - Complex.I * y = Complex.I * (x - y) := by
  simp [mul_sub]

lemma helper_re_of_w (z h : ℂ) : (((((z + h).re : ℂ) + Complex.I * z.im)).re) = (z + h).re := by
  simp

lemma diff_If_zh_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  classical
  intro w
                              
  let g : ℝ → ℂ := fun τ => f (((z + h).re : ℂ) + Complex.I * τ)
                                                              
  have hInt1 : IntervalIntegrable g volume (0 : ℝ) ((z + h).im) := by
    simpa [g] using
      (vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (a := z + h) hzh)
  have hInt2 : IntervalIntegrable g volume (0 : ℝ) (z.im) := by
    have hInt2' :
        IntervalIntegrable
          (fun τ : ℝ => f (((( (((z + h).re : ℂ) + Complex.I * z.im)).re : ℂ)) + Complex.I * τ))
          volume (0 : ℝ) (((((z + h).re : ℂ) + Complex.I * z.im)).im) :=
      vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf
        (a := (((z + h).re : ℂ) + Complex.I * z.im)) hw
    simpa [g, helper_re_of_w z h, helper_im_of_w z h] using hInt2'
  have hinterval :
      ((∫ τ in (0 : ℝ)..(z + h).im, g τ) - ∫ τ in (0 : ℝ)..z.im, g τ)
      = ∫ τ in z.im..(z + h).im, g τ :=
    intervalIntegral.integral_interval_sub_left (μ := volume) (f := g) hInt1 hInt2
                                          
  have h1 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ) := by
    have hzph := def_If_z_plus_h hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (z := z) (h := h) hz hzh
    simpa [g] using hzph
  have h2 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ) := by
    have hwdef := def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
    simpa [g, w] using hwdef
                                                           
  calc
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [h1, h2]
    _ = (Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - (Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = Complex.I *
          ((∫ τ in (0 : ℝ)..(z + h).im, g τ)
            - (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [helper_mul_sub_complex]
    _ = Complex.I * (∫ τ in z.im..(z + h).im, g τ) := by
      simpa using congrArg (fun t => Complex.I * t) hinterval
    _ = Complex.I * (∫ τ in z.im..(z + h).im,
          f (((z + h).re : ℂ) + Complex.I * τ)) := by
      simp [g]


lemma diff_If_w_z_initial_form
  {r1 R R0 : ℝ}
  (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z h : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
  (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..w.re, f (t : ℂ))
      + Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (w.re + Complex.I * τ) - f (z.re + Complex.I * τ))) := by
  intro w

  rw [def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
  rw [def_If_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz]

  have hw_re : w.re = (z + h).re := by simp [w]
  have hw_im : w.im = z.im := by simp [w]

  have step1 :
    ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
      - ((∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
      + Complex.I * ((∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
        - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))) := by ring
  rw [step1]

  have horizontal_integrable_zh : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) (z + h).re := by
                                                                          
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
                                                                  
    have : ‖z + h‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hzh
    have : |(z + h).re| ≤ ‖z + h‖ := Complex.abs_re_le_norm (z + h)
    have : |t| ≤ |(z + h).re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_integrable_z : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) z.re := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
    have : ‖z‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hz
    have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have : |t| ≤ |z.re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_eq :
    (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
    = ∫ t in z.re..(z + h).re, f (t : ℂ) := by
    rw [← intervalIntegral.integral_interval_sub_left horizontal_integrable_zh horizontal_integrable_z]

  have vertical_integrable_zh : IntervalIntegrable (fun τ : ℝ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
                                                     
    rw [← hw_re, ← hw_im]
    exact vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hw

  have vertical_integrable_z : IntervalIntegrable (fun τ : ℝ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im :=
    vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz

  have vertical_eq :
    (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
      - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = ∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)) := by
    rw [← intervalIntegral.integral_sub vertical_integrable_zh vertical_integrable_z]

  rw [horizontal_eq, vertical_eq, hw_re]


lemma algebraic_rearrangement_four_terms (a b c d : ℂ) :
    a - b + c - d = 0 → c - d = b - a := by
  intro h

  calc c - d
    = (a - b + c - d) - (a - b) := by ring
    _ = 0 - (a - b) := by rw [h]
    _ = -(a - b) := by ring
    _ = b - a := by ring

lemma real_between_as_convex_combination (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ t = (1 - lam) * b₁ + lam * b₂ := by
                                                        
  cases' le_total b₁ b₂ with h₁ h₂
  case inl =>

    have ht : b₁ ≤ t ∧ t ≤ b₂ := by
      cases' h with h_left h_right
      · exact h_left
      ·                                                                           
        exact ⟨le_trans h₁ h_right.1, le_trans h_right.2 h₁⟩

    by_cases heq : b₁ = b₂
    ·                                              
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [heq] at ht ⊢
        have : t = b₂ := le_antisymm ht.2 ht.1
        rw [this]
        ring
    ·                            
      have hlt : b₁ < b₂ := lt_of_le_of_ne h₁ heq
      let lam := (t - b₁) / (b₂ - b₁)
      use lam
      constructor
      ·           
        apply div_nonneg
        · linarith [ht.1]
        · linarith [hlt]
      constructor
      ·                              
        rw [div_le_iff₀]
        · linarith [ht.2]                                         
        · linarith [hlt]                 
      ·                                 
        unfold lam
        have h_nonzero : b₂ - b₁ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero]; ring
  case inr =>

    have ht : b₂ ≤ t ∧ t ≤ b₁ := by
      cases' h with h_left h_right
      ·                                                                           
        exact ⟨le_trans h₂ h_left.1, le_trans h_left.2 h₂⟩
      · exact h_right

    by_cases heq : b₁ = b₂
    ·                                              
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [← heq] at ht ⊢
        have : t = b₁ := le_antisymm ht.2 ht.1
        rw [this, heq]
        ring
    ·                            
      have hlt : b₂ < b₁ := lt_of_le_of_ne h₂ (Ne.symm heq)
      let lam := (b₁ - t) / (b₁ - b₂)
      use lam
      constructor
      ·           
        apply div_nonneg
        · linarith [ht.2]                           
        · linarith [hlt]                 
      constructor
      ·                              
        rw [div_le_iff₀]
        · linarith [ht.1]                                         
        · linarith [hlt]                 
      ·                                 
        unfold lam
        have h_nonzero : b₁ - b₂ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero]; ring

lemma convex_combination_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : E) (t : ℝ)
  (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
  (1 - t) • x + t • y ∈ segment ℝ x y := by

  use (1 - t), t
  constructor
  ·             
    linarith [h₁]
  constructor
  ·         
    exact h₀
  constructor
  ·                   
    ring
  ·                                             
    rfl

lemma vertical_line_in_segment (a : ℂ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  a + Complex.I * t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
                                                
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h

  have h_convex : a + Complex.I * t = (1 - lam) • (a + Complex.I * b₁) + lam • (a + Complex.I * b₂) := by
                                           
    simp only [Complex.real_smul]
                                               
    rw [h_t_eq]
                                 
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
                                                                              
    rw [mul_add]
                                                      
    ring

  rw [h_convex]
  exact convex_combination_mem_segment (a + Complex.I * b₁) (a + Complex.I * b₂) lam h_lam_nonneg h_lam_le_one

lemma horizontal_line_in_segment (a : ℝ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  (t : ℂ) + Complex.I * a ∈ segment ℝ ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) := by
                                                     
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h
                                                                        
  have h_convex : (t : ℂ) + Complex.I * a
      = (1 - lam) • ((b₁ : ℂ) + Complex.I * a) + lam • ((b₂ : ℂ) + Complex.I * a) := by
    simp only [Complex.real_smul]
                   
    rw [h_t_eq]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
                                       
  simpa [h_convex] using
    (convex_combination_mem_segment ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) lam h_lam_nonneg h_lam_le_one)

lemma intervalIntegrable_of_continuousOn_range (f : ℂ → ℂ) (g : ℝ → ℂ) (a b : ℝ) (S : Set ℂ)
  (hf : ContinuousOn f S) (hg : Continuous g)
  (hrange : ∀ t ∈ Set.uIcc a b, g t ∈ S) :
  IntervalIntegrable (f ∘ g) volume a b := by
                                                           
  have h_comp : ContinuousOn (f ∘ g) (Set.uIcc a b) := by
    apply ContinuousOn.comp hf (hg.continuousOn) hrange
                                                                     
  exact h_comp.intervalIntegrable

lemma intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {a : ℂ} {b₁ b₂ : ℝ}
  (h₁ : ‖a + Complex.I * b₁‖ ≤ r1) (h₂ : ‖a + Complex.I * b₂‖ ≤ r1) :
  IntervalIntegrable (fun t => f (a + Complex.I * t)) volume b₁ b₂ := by
                                                                    
  apply intervalIntegrable_of_continuousOn_range f (fun t => a + Complex.I * ↑t) b₁ b₂ (Metric.closedBall (0 : ℂ) R)
  ·                                                                              
    exact AnalyticOnNhd.continuousOn hf
  ·                                               
    exact Continuous.add continuous_const (Continuous.mul continuous_const continuous_ofReal)
  ·                                                         
    intro t ht
                                                                       
    have h_in_r1 : ‖a + Complex.I * ↑t‖ ≤ r1 := by
                                                            
      have h_segment : a + Complex.I * ↑t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
        apply vertical_line_in_segment
        exact Set.mem_uIcc.mp ht
                                                              
      have h₁_mem : a + Complex.I * b₁ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : a + Complex.I * b₂ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
                                         
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
                                                              
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

lemma cauchy_for_rectangles
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r1)
    (hzw : ((w.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1)
    (hwz : ((z.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (z.im)))
    - (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (w.im)))
    + Complex.I * (∫ y in z.im..w.im, f ((w.re : ℂ) + Complex.I * y))
    - Complex.I * (∫ y in z.im..w.im, f ((z.re : ℂ) + Complex.I * y)) = 0 := by
  classical
                                                                                    
  have hA : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                          
    have hz_eq : z = (z.re : ℂ) + Complex.I * z.im := by
      exact (lem_wReIm z)
    rwa [← hz_eq]
  have hC : ((w.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                          
    have hw_eq : w = (w.re : ℂ) + Complex.I * w.im := by
      exact (lem_wReIm w)
    rwa [← hw_eq]
                                                                                                
  have h_left_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (z.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im) ((z.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (z.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hA hwz hseg
  have h_right_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (w.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((w.re : ℂ) + Complex.I * z.im) ((w.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (w.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hzw hC hseg
  have h_point_in_ball : ∀ x ∈ Set.uIcc z.re w.re, ∀ y ∈ Set.uIcc z.im w.im,
      ((x : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro x hx y hy
    have hL : ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_left_in_ball y hy
    have hR' : ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_right_in_ball y hy
                                                                
    obtain ⟨lam, hlam0, hlam1, hx_eq⟩ := real_between_as_convex_combination z.re w.re x (Set.mem_uIcc.mp hx)
    have hseg_horiz : (x : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
                                    
      have : (x : ℂ) + Complex.I * (y : ℂ)
          = (1 - lam) • ((z.re : ℂ) + Complex.I * (y : ℂ)) + lam • ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
        simp only [Complex.real_smul]
                                                    
        rw [hx_eq]
        simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      simpa [this] using
        (convex_combination_mem_segment ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) lam hlam0 hlam1)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hL hR' hseg_horiz
                                                                
  set S := ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
  have hS_subset_r1 : S ⊆ Metric.closedBall (0 : ℂ) r1 := by
    intro p hp
    have hx : p.re ∈ [[z.re, w.re]] := hp.1
    have hy : p.im ∈ [[z.im, w.im]] := hp.2
                                                              
    have : ((p.re : ℂ) + Complex.I * (p.im : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 :=
      h_point_in_ball p.re hx p.im hy
                                                                       
    have hp_eq : p = (p.re : ℂ) + Complex.I * (p.im : ℂ) := lem_wReIm p
    rwa [hp_eq]
  have hS_subset_R : S ⊆ Metric.closedBall (0 : ℂ) R :=
    fun p hp => (closedBall_mono_center0 (le_of_lt hr1_lt_R)) (hS_subset_r1 hp)
                                                                               
  have Hdiff : DifferentiableOn ℂ f S := by
    intro p hp
    have hpR : p ∈ Metric.closedBall (0 : ℂ) R := hS_subset_R hp
    exact (hf p hpR).differentiableAt.differentiableWithinAt
                                                          
  simpa [smul_eq_mul, mul_comm] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w Hdiff

lemma cauchy_for_horizontal_strip
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    - (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) = 0 := by
                                                                               
  let z₀ : ℂ := (z.re : ℂ)
  let w₀ : ℂ := (z + h).re + Complex.I * z.im
                         
  have hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r1 := by
    have hz_norm : ‖z‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzre_le : ‖(z.re : ℂ)‖ ≤ ‖z‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm z
    have : ‖z₀‖ ≤ r1 := le_trans hzre_le hz_norm
    simpa [z₀, Metric.mem_closedBall, dist_eq_norm] using this
  have hw₀ : w₀ ∈ Metric.closedBall (0 : ℂ) r1 := hw
                                                  
  have hzw : ((w₀.re : ℂ) + Complex.I * z₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                                                          
    have h1 : ((w₀.re : ℂ) + Complex.I * z₀.im) = ((z + h).re : ℂ) := by
      simp [w₀, z₀, Complex.ofReal_im, mul_zero, add_zero]
    rw [h1]
    have h2 : ‖((z + h).re : ℂ)‖ ≤ ‖z + h‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm (z + h)
    have h3 : ‖z + h‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzh
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_trans h2 h3
  have hwz : ((z₀.re : ℂ) + Complex.I * w₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                                            
    have h1 : ((z₀.re : ℂ) + Complex.I * w₀.im) = z := by
      simp [z₀, w₀, Complex.ofReal_re]
      exact (lem_wReIm z).symm
    rw [h1]
    exact hz
                                   
  have H := cauchy_for_rectangles (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz₀ hw₀ hzw hwz

  rw [(show z₀.re = z.re by simp [z₀])] at H
  rw [(show z₀.im = (0 : ℝ) by simp [z₀])] at H
  rw [(show w₀.re = (z + h).re by simp [w₀])] at H
  rw [(show w₀.im = z.im by simp [w₀])] at H

  convert (preTransparency := .instances) H using 1
  simp only [Complex.ofReal_zero, mul_zero, add_zero]

lemma integrability_from_cauchy_horizontal_strip
    {r1 R R0 : ℝ} (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r1) (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im ∧
    IntervalIntegrable (fun τ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
  constructor
  ·                                                         
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    ·                                           
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hzh
      exact le_trans (Complex.abs_re_le_norm (z + h)) hzh
    ·                                              
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact hw
  ·                                                    
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    ·                                     
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact le_trans (Complex.abs_re_le_norm z) hz
    ·                                        
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [← lem_wReIm z]
      exact hz

lemma cauchy_rearrangement_step1
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)))
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) - (∫ t in z.re..(z + h).re, f (t : ℂ)) := by
                                   
  have H := cauchy_for_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have integrable := integrability_from_cauchy_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have rearrange := algebraic_rearrangement_four_terms
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    H

  have vertical_linearity :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ))) := by
    rw [← mul_sub]
    rw [← intervalIntegral.integral_sub integrable.1 integrable.2]

  rw [← vertical_linearity]
  exact rearrange

lemma diff_If_w_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by

  have initial_form := diff_If_w_z_initial_form hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have rearrange_step := cauchy_rearrangement_step1 hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have w_re_eq : (((z + h).re : ℂ) + Complex.I * z.im).re = (z + h).re := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]

  simp_rw [initial_form, w_re_eq, rearrange_step]

  ring

lemma If_difference_is_L_path_integral
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
      + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by

  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im

  calc If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
       - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
     = (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩)
       + (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
          - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩) := by ring
     _ = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ))
       + (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by
       rw [diff_If_zh_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw,
           diff_If_w_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
     _ = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
       + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by ring

lemma If_diff_add_sub_identity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z) + f z)
    + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) := by
                                                                                               
  have H :=
    If_difference_is_L_path_integral (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one) hf hz hzh hw
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using H

lemma intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {im_part : ℝ} {a b : ℝ}
  (h₁ : ‖(a : ℂ) + Complex.I * im_part‖ ≤ r1) (h₂ : ‖(b : ℂ) + Complex.I * im_part‖ ≤ r1) :
  IntervalIntegrable (fun t => f ((t : ℂ) + Complex.I * im_part)) volume a b := by
                                                                    
  apply intervalIntegrable_of_continuousOn_range f (fun t => (t : ℂ) + Complex.I * im_part) a b (Metric.closedBall (0 : ℂ) R)
  ·                                                                              
    exact AnalyticOnNhd.continuousOn hf
  ·                                                                     
    exact Continuous.add continuous_ofReal continuous_const
  ·                                                         
    intro t ht
                                                                       
    have h_in_r1 : ‖(t : ℂ) + Complex.I * im_part‖ ≤ r1 := by
                                                            
      have h_segment : (t : ℂ) + Complex.I * im_part ∈ segment ℝ ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) := by

        obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination a b t (Set.mem_uIcc.mp ht)

        have h_convex : (t : ℂ) + Complex.I * im_part = (1 - lam) • ((a : ℂ) + Complex.I * im_part) + lam • ((b : ℂ) + Complex.I * im_part) := by
                                                 
          simp only [Complex.real_smul]
                                                   
          rw [h_t_eq]
                                       
          simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
                                             
          ring

        rw [h_convex]
        exact convex_combination_mem_segment ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) lam h_lam_nonneg h_lam_le_one

      have h₁_mem : (a : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : (b : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
                                         
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
                                                              
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

lemma If_diff_linearity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    ((∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
     + (∫ _t in z.re..(z + h).re, f z))
    + Complex.I *
      ((∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))
       + (∫ _τ in z.im..(z + h).im, f z)) := by
                                                                                             
  have H := If_diff_add_sub_identity hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have hz_norm : ‖z‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
  have hzh_norm : ‖z + h‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzh
  have hw_norm : ‖((z + h).re : ℂ) + Complex.I * z.im‖ ≤ r1 := by
    rwa [Metric.mem_closedBall, dist_zero_right] at hw

  have h_z_eq : z = (z.re : ℂ) + Complex.I * z.im := lem_wReIm z
  have h_zh_eq : z + h = ((z + h).re : ℂ) + Complex.I * (z + h).im := lem_wReIm (z + h)

  have hz_endpoint : ‖(z.re : ℂ) + Complex.I * z.im‖ ≤ r1 := by rwa [← h_z_eq]
  have h_horiz_integrable := intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
    hr1_lt_R hf hz_endpoint hw_norm

  have hzh_endpoint : ‖((z + h).re : ℂ) + Complex.I * (z + h).im‖ ≤ r1 := by rwa [← h_zh_eq]
  have h_vert_integrable := intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
    hr1_lt_R hf hw_norm hzh_endpoint

  have h_const_horiz : IntervalIntegrable (fun _ => f z) volume z.re (z + h).re := intervalIntegrable_const
  have h_const_vert : IntervalIntegrable (fun _ => f z) volume z.im (z + h).im := intervalIntegrable_const

  have h_diff_horiz : IntervalIntegrable (fun t => f (t + Complex.I * z.im) - f z) volume z.re (z + h).re :=
    IntervalIntegrable.sub h_horiz_integrable h_const_horiz

  have h_diff_vert : IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ) - f z) volume z.im (z + h).im :=
    IntervalIntegrable.sub h_vert_integrable h_const_vert

  have h1 : ∫ t in z.re..(z + h).re, ((f (t + Complex.I * z.im) - f z) + f z) =
           (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)) + (∫ t in z.re..(z + h).re, f z) :=
    intervalIntegral.integral_add h_diff_horiz h_const_horiz

  have h2 : ∫ τ in z.im..(z + h).im, ((f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) =
           (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)) + (∫ τ in z.im..(z + h).im, f z) :=
    intervalIntegral.integral_add h_diff_vert h_const_vert

  rw [H, h1, h2, mul_add]

lemma integral_of_constant_over_L_path
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (_hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ _t in z.re..(z + h).re, f z) + Complex.I * (∫ _τ in z.im..(z + h).im, f z)
      = f z * h := by
                                                           
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const]

  rw [Complex.add_re, Complex.add_im]
  simp only [add_sub_cancel_left]

  rw [Complex.real_smul, Complex.real_smul]

  rw [← mul_assoc]

  rw [← add_mul]

  rw [mul_comm Complex.I (↑h.im)]

  rw [Complex.re_add_im h]

  rw [mul_comm]



lemma If_diff_decomposition_final
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = f z * h
      + Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
                                                                                      
  have H :=
    If_diff_linearity (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one)
      (f := f) (hf := hf)
      (z := z) (h := h)
      (hz := hz) (hzh := hzh) (hw := hw)
                                                                   
  let A : ℂ := ∫ t in z.re..(z + h).re, f (t + Complex.I * z.im) - f z
  let B : ℂ := ∫ t in z.re..(z + h).re, f z
  let C : ℂ := ∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ) - f z
  let D : ℂ := ∫ τ in z.im..(z + h).im, f z
                                                                    
  have hH' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + B) + Complex.I * (C + D) := by
    simpa [A, B, C, D, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using H
                                                                          
  have hsplit : (A + B) + Complex.I * (C + D)
      = (A + Complex.I * C) + (B + Complex.I * D) := by ring
  have hH'' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + (B + Complex.I * D) := by
    simpa [hsplit] using hH'
                                                               
  have hBD : (B + Complex.I * D) = f z * h := by
    simpa [B, D] using
      integral_of_constant_over_L_path (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh
  have hH''' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + f z * h := by
    simpa [hBD] using hH''
                                                                
  have hH4 : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h + f z * h := by
    simpa [Err, A, C, add_comm, add_left_comm, add_assoc] using hH'''
                                                         
  simpa [Err, add_comm, add_left_comm, add_assoc] using hH4




lemma bound_on_Err
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖
      ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := by
                                                          
  unfold Err
                                    
  have hsplit :
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
      ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
        + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ :=
    norm_add_le _ _

  have hI : ‖Complex.I‖ = (1 : ℝ) := by simp
  have hvertnorm :
      ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
        = ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by
    simp [hI, one_mul]

  set SH : Set ℝ := {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
      r = ‖f (t + Complex.I * z.im) - f z‖}
  have hbdd_SH : BddAbove SH := by
    classical
                                                
    have hK : IsCompact (Set.uIcc z.re (z + h).re) := isCompact_uIcc
                                  
    let γ : ℝ → ℂ := fun t => (t : ℂ) + Complex.I * z.im
    have hγ_cont : Continuous γ := by
      convert (preTransparency := .instances) (Complex.continuous_ofReal.add (continuous_const (y := Complex.I * (z.im : ℂ)))) using 1
    have hz_mem : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show (z.re : ℂ) + Complex.I * z.im = z.re + z.im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have hw_mem : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hw
    have hseg_subset :
        (γ '' Set.uIcc z.re (z + h).re) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim
      rcases hwim with ⟨t, ht, rfl⟩
                                                                  
      have hseg : ((t : ℂ) + Complex.I * z.im)
          ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * z.im) := by

        have := horizontal_line_in_segment (a := z.im) (b₁ := z.re) (b₂ := (z + h).re)
          (t := t) (by simpa [Set.mem_uIcc] using ht)
        simpa using this
      have hz_in : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hz_mem
      have hw_in : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hw_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simpa [Metric.mem_closedBall, dist_zero_right] using hw'
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
                                                        
    have hmaps : Set.MapsTo γ (Set.uIcc z.re (z + h).re) (Metric.closedBall (0 : ℂ) R) := by
      intro t ht
      have himg_r1 : γ t ∈ Metric.closedBall (0 : ℂ) r1 := by
        exact hseg_subset (Set.mem_image_of_mem _ ht)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) himg_r1
    have hcont_on : ContinuousOn (fun t => f (γ t)) (Set.uIcc z.re (z + h).re) := by
      convert (preTransparency := .instances) (ContinuousOn.comp (hf_cont) (hγ_cont.continuousOn) hmaps) using 1; rfl
                                                         
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun t => ‖f (γ t) - f z‖) (Set.uIcc z.re (z + h).re) := by
                                              
      have h_cont_sub : ContinuousOn (fun t => f (γ t) - f z) (Set.uIcc z.re (z + h).re) :=
        hcont_on.sub continuousOn_const
                        
      exact h_cont_sub.norm
                                            
    have himage_compact : IsCompact ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      IsCompact.image_of_continuousOn hK hR_cont
                                    
    have hSH_eq : SH = (fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re := by
      ext r; constructor
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
                                           
    have : BddAbove ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      himage_compact.bddAbove
    simpa [hSH_eq] using this

  set SV : Set ℝ := {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
      r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}
  have hbdd_SV : BddAbove SV := by
    classical
                                          
    have hK : IsCompact (Set.uIcc z.im (z + h).im) := isCompact_uIcc
    let γv : ℝ → ℂ := fun τ => ((z + h).re : ℂ) + Complex.I * τ
    have hγv_cont : Continuous γv := by
      have hmul : Continuous (fun τ : ℝ => Complex.I * (τ : ℂ)) := by
        exact continuous_const.mul Complex.continuous_ofReal
      simp only [γv]
      exact continuous_const.add hmul
    have hw_mem' : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have hzh_mem : (((z + h).re : ℂ) + Complex.I * (z + h).im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show ((z + h).re : ℂ) + Complex.I * (z + h).im = (z + h).re + (z + h).im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hzh
    have hseg_subset :
        (γv '' Set.uIcc z.im (z + h).im) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim; rcases hwim with ⟨τ, hτ, rfl⟩
      have hseg : (((z + h).re : ℂ) + Complex.I * τ)
          ∈ segment ℝ (((z + h).re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * (z + h).im) := by
        have := vertical_line_in_segment (((z + h).re : ℂ)) (b₁ := z.im) (b₂ := (z + h).im) (t := τ)
          (by simpa [Set.mem_uIcc] using hτ)
        simpa using this
      have hz_in := hw_mem'
      have hw_in := hzh_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simp only [Metric.mem_closedBall, dist_zero_right] at hw'
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hmaps : Set.MapsTo γv (Set.uIcc z.im (z + h).im) (Metric.closedBall (0 : ℂ) R) := by
      intro τ hτ; have : γv τ ∈ Metric.closedBall (0 : ℂ) r1 := hseg_subset (Set.mem_image_of_mem _ hτ)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) this
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
    have hcont_on : ContinuousOn (fun τ => f (γv τ)) (Set.uIcc z.im (z + h).im) := by
      convert (preTransparency := .instances) (ContinuousOn.comp (hf_cont) (hγv_cont.continuousOn) hmaps) using 1; rfl
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun τ => ‖f (γv τ) - f z‖) (Set.uIcc z.im (z + h).im) := by
      have h1 : ContinuousOn (fun τ => f (γv τ) - f z) (Set.uIcc z.im (z + h).im) := by
        exact hcont_on.sub continuousOn_const
      exact h1.norm
    have himage_compact : IsCompact ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      IsCompact.image_of_continuousOn hK hR_cont
    have hSV_eq : SV = (fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im := by
      ext r; constructor
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
    have : BddAbove ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      himage_compact.bddAbove
    simpa [hSV_eq] using this

  have hC_horiz : ∀ t ∈ Set.uIcc z.re (z + h).re,
      ‖(f (t + Complex.I * z.im) - f z)‖ ≤ S_horiz z h f := by
    intro t ht
    have hx : ‖f (t + Complex.I * z.im) - f z‖ ∈ SH := ⟨t, ht, rfl⟩
                                              
    have : S_horiz z h f = sSup SH := rfl
    simpa [this] using (le_csSup hbdd_SH hx)

  have hC_vert : ∀ τ ∈ Set.uIcc z.im (z + h).im,
      ‖(f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ S_vert z h f := by
    intro τ hτ
    have hx : ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖ ∈ SV := ⟨τ, hτ, rfl⟩
    have : S_vert z h f = sSup SV := rfl
    simpa [this] using (le_csSup hbdd_SV hx)

  have hH : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            ≤ |(z + h).re - z.re| * S_horiz z h f := by
                                           
    have h_bound : ∀ t, t ∈ [[z.re, (z + h).re]] → ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht; exact hC_horiz t ht
    have h_int : ∀ t ∈ Ι z.re (z + h).re, ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht
      have ht_uIcc : t ∈ Set.uIcc z.re (z + h).re := by
                                             
        exact Set.uIoc_subset_uIcc ht
      exact h_bound t ht_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    convert (preTransparency := .instances) this using 1
    ring

  have hV : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
            ≤ |(z + h).im - z.im| * S_vert z h f := by
    have h_bound : ∀ τ, τ ∈ [[z.im, (z + h).im]] → ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ; exact hC_vert τ hτ
    have h_int : ∀ τ ∈ Ι z.im (z + h).im, ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ
      have hτ_uIcc : τ ∈ Set.uIcc z.im (z + h).im := by
                                             
        exact Set.uIoc_subset_uIcc hτ
      exact h_bound τ hτ_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    rwa [mul_comm] at this

  have hre' : (z + h).re - z.re = h.re := by
    simp [Complex.add_re]
  have him' : (z + h).im - z.im = h.im := by
    simp [Complex.add_im]
  have hre : |(z + h).re - z.re| = |h.re| := by simp
  have him : |(z + h).im - z.im| = |h.im| := by simp

  have hH' : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
                ≤ |h.re| * S_max z h f := by
    have : S_horiz z h f ≤ S_max z h f := by exact le_max_left _ _
                                 
    have hH_rewritten : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖ ≤ |h.re| * S_horiz z h f := by
      rwa [hre] at hH
                           
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.re))
    exact le_trans hH_rewritten h_bound

  have hV' : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
                ≤ |h.im| * S_max z h f := by
    have : S_vert z h f ≤ S_max z h f := by exact le_max_right _ _
                                 
    have hV_rewritten : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ |h.im| * S_vert z h f := by
      rwa [him] at hV
                           
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.im))
    exact le_trans hV_rewritten h_bound

  have :=
    calc
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
          ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ := hsplit
      _ = ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by simp
      _ ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := add_le_add hH' hV'

  simpa [Err] using this

lemma S_horiz_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_horiz z h f := by
                                                         
  unfold S_horiz
  apply Real.sSup_nonneg
  intro r hr; rcases hr with ⟨t, ht, rfl⟩; exact norm_nonneg _

lemma S_max_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_max z h f := by
  unfold S_max
  have h1 : 0 ≤ S_horiz z h f := S_horiz_nonneg z h f
  exact le_trans h1 (le_max_left _ _)

lemma bound_on_Err_ratio
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1)
    (hh : h ≠ 0) :
    ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤ 2 * S_max z h f := by

  have h_abs_eq : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ = ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ := rfl

  have h1 := bound_on_Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
                                                                                  
  rw [← add_mul] at h1

  have h_norm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh

  have h2 : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖ / ‖h‖ ≤
            (|h.re| + |h.im|) * S_max z h f / ‖h‖ := by
    exact div_le_div_of_nonneg_right h1 (le_of_lt h_norm_pos)

  rw [← norm_div] at h2

  have h2' : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤
             (|h.re| + |h.im|) / ‖h‖ * S_max z h f := by
    rw [← div_mul_eq_mul_div] at h2
    exact h2

  have h3 : |h.re| + |h.im| ≤ 2 * ‖h‖ := by
                                                                
    calc |h.re| + |h.im|
      ≤ ‖h‖ + ‖h‖ := add_le_add (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
      _ = 2 * ‖h‖ := by ring

  have h4 : (|h.re| + |h.im|) / ‖h‖ ≤ 2 := by
                                                                                         
    rw [div_le_iff₀ h_norm_pos]
    exact h3

  calc ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖
    ≤ (|h.re| + |h.im|) / ‖h‖ * S_max z h f := h2'
    _ ≤ 2 * S_max z h f := mul_le_mul_of_nonneg_right h4 (S_max_nonneg z h f)
open _root_.Filter _root_.Topology

lemma abs_horizontal_diff_eq_abs_real (z : ℂ) (t : ℝ) : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := by
                                                           
  have h : (t : ℂ) + Complex.I * z.im - z = (t - z.re : ℂ) := by
    apply Complex.ext_iff.mpr
    constructor
    ·                                      
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                 Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring
    ·                                       
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
                 Complex.I_re, Complex.I_im, Complex.ofReal_re]
      ring

  rw [h]
                                                                         
  rw [← Complex.ofReal_sub]
                                                                             
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma abs_sub_le_of_mem_uIcc (a b t : ℝ) (ht : t ∈ Set.uIcc a b) : |t - a| ≤ |b - a| ∧ |b - t| ≤ |b - a| := by
                                                  
  have h1 : a ≤ b ∨ b ≤ a := le_total a b
  rcases h1 with hle | hle
  ·                             
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : a ≤ t ∧ t ≤ b := by simpa using ht'
    constructor
    · have h_ta : |t - a| = t - a := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.left)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_right h_bounds.right a
    · have h_bt : |b - t| = b - t := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.right)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_left h_bounds.left b
  ·                         
    have ht' : t ∈ Set.Icc b a := by
      rw [Set.uIcc_comm] at ht
      simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : b ≤ t ∧ t ≤ a := by simpa using ht'
    constructor
    · have h_ta : |t - a| = a - t := by simp [abs_of_nonpos (sub_nonpos.mpr h_bounds.right)]
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_left h_bounds.left a
    · have h_bt : |b - t| = t - b := by
        rw [abs_of_nonpos (sub_nonpos.mpr h_bounds.left)]
        ring
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_right h_bounds.right b







lemma abs_vertical_core (z h : ℂ) (τ : ℝ) : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| := by
                                                                           
  have h1 : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |((h.re : ℝ) + Complex.I * (τ - z.im)).re| + |((h.re : ℝ) + Complex.I * (τ - z.im)).im| := by
    apply Complex.norm_le_abs_re_add_abs_im

  have h2 : ((h.re : ℝ) + Complex.I * (τ - z.im)).re = h.re := by simp
  have h3 : ((h.re : ℝ) + Complex.I * (τ - z.im)).im = τ - z.im := by simp

  rw [h2, h3] at h1
  exact h1



lemma mem_closedBall_mono_radius {z : ℂ} {r R : ℝ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) (h : r ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using le_trans (by simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz) h

lemma tendsto_of_nonneg_local_bound {g : ℂ → ℝ}
  (h_nonneg : ∀ h, 0 ≤ g h)
  (h_loc : ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ < δ → g h ≤ ε) :
  Tendsto g (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
                                                       
  have hε_half : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ, hδ_pos, hδ⟩ := h_loc (ε / 2) hε_half
  use δ
  exact ⟨hδ_pos, fun h hh_dist => by
    rw [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (h_nonneg h)]
    have : g h ≤ ε / 2 := hδ h (by rwa [Complex.dist_eq, sub_zero] at hh_dist)
    linarith⟩

lemma sum_abs_le_two_mul {x y A : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ A) : |x| + |y| ≤ (2:ℝ) * A := by
  have := add_le_add hx hy
  simpa [two_mul] using this

lemma two_norm_lt_of_norm_lt_half {h : ℂ} {δ : ℝ} (_hpos : 0 < δ) (hbound : ‖h‖ < δ/2) : (2:ℝ) * ‖h‖ < δ := by
  have := mul_lt_mul_of_pos_left hbound (by norm_num : (0:ℝ) < 2)
  simpa [two_mul, add_halves] using this

lemma limit_of_S_is_zero
    {r1 R R0 : ℝ}
  (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) := by
                                                                  
  have f_cont_at_z : ContinuousAt f z := by
                                                                     
    have hz_in_R : z ∈ Metric.closedBall (0 : ℂ) R :=
      mem_closedBall_mono_radius hz (le_of_lt hr1_lt_R)
                                        
    exact (hf z hz_in_R).continuousAt

  apply tendsto_of_nonneg_local_bound
  ·                                  
    exact fun h => S_max_nonneg z h f
  ·                                                                   
    intro ε hε_pos
                                        
    rw [Metric.continuousAt_iff] at f_cont_at_z
    obtain ⟨δ₁, hδ₁_pos, hf_bound⟩ := f_cont_at_z ε hε_pos

    use δ₁ / 2
    constructor
    · exact half_pos hδ₁_pos
    · intro h hh_norm

      unfold S_max
      apply max_le

      · unfold S_horiz
                                                 
        apply Real.sSup_le
        ·                                        
          intro r hr
          obtain ⟨t, ht, rfl⟩ := hr

          have key_dist : dist ((t : ℂ) + Complex.I * z.im) z < δ₁ := by
                                                                     
            rw [dist_eq]
                                                                         
            have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := abs_horizontal_diff_eq_abs_real z t
            simp [eq_transform]
                                                                
            have t_bound : |t - z.re| ≤ |(z + h).re - z.re| := (abs_sub_le_of_mem_uIcc z.re (z + h).re t ht).1
            have re_diff_le : |(z + h).re - z.re| ≤ ‖h‖ := by
                                       
              simpa [Complex.add_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Complex.abs_re_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            calc |t - z.re|
              _ ≤ |(z + h).re - z.re| := t_bound
              _ ≤ ‖h‖ := re_diff_le
              _ < δ₁ / 2 := h_bound
              _ < δ₁ := by linarith
                                              
          have f_dist := hf_bound key_dist
                                                         
          rw [dist_eq] at f_dist
                                 
          exact le_of_lt f_dist
        ·              
          exact le_of_lt hε_pos

      · unfold S_vert
        apply Real.sSup_le
        ·                                        
          intro r hr
          obtain ⟨τ, hτ, rfl⟩ := hr
                                                    
          have key_dist : dist (((z + h).re : ℂ) + Complex.I * τ) z < δ₁ := by
            rw [dist_eq]

            have h_eq : (((z + h).re : ℂ) + Complex.I * τ - z) = (h.re : ℝ) + Complex.I * (τ - z.im) := by
              apply Complex.ext_iff.mpr
              constructor
              · simp [Complex.add_re, Complex.sub_re]
              · simp [Complex.add_im, Complex.sub_im]
            rw [h_eq]
                                                             
            have τ_bound0 : |τ - z.im| ≤ |(z + h).im - z.im| := (abs_sub_le_of_mem_uIcc z.im (z + h).im τ hτ).1
            have im_diff_eq : |(z + h).im - z.im| = |h.im| := by
              simp [Complex.add_im, sub_eq_add_neg, add_assoc]
            have τ_bound : |τ - z.im| ≤ |h.im| := by simpa [im_diff_eq] using τ_bound0
                                                                 
            have vertical_bound : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| :=
              abs_vertical_core z h τ
            have sum_bound : |h.re| + |τ - z.im| ≤ |h.re| + |h.im| := by
              exact add_le_add_right τ_bound _
            have norm_bound := sum_abs_le_two_mul (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            have final_bound := two_norm_lt_of_norm_lt_half hδ₁_pos h_bound
            calc ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖
              _ ≤ |h.re| + |τ - z.im| := vertical_bound
              _ ≤ |h.re| + |h.im| := sum_bound
              _ ≤ (2 : ℝ) * ‖h‖ := norm_bound
              _ < δ₁ := final_bound
                                              
          have f_dist := hf_bound key_dist
          rw [dist_eq] at f_dist
                                 
          exact le_of_lt f_dist
        ·              
          exact le_of_lt hε_pos

lemma eventually_corner_and_sum_in_closedBall {z : ℂ} {R' : ℝ}
  (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    (z + h) ∈ Metric.closedBall (0 : ℂ) R' ∧
    (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) R' := by
                         
  have hρ_pos : 0 < R' - ‖z‖ := sub_pos.mpr hz
  have h_small : ∀ᶠ h in 𝓝 (0:ℂ), h ∈ Metric.ball (0 : ℂ) (R' - ‖z‖) :=
    Metric.ball_mem_nhds (0 : ℂ) hρ_pos
  refine h_small.mono ?_
  intro h hhball
  have hnorm_lt : ‖h‖ < R' - ‖z‖ := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hhball
                                              
  have hsum_lt : ‖z‖ + ‖h‖ < R' := by
    have htemp : ‖z‖ + ‖h‖ < ‖z‖ + (R' - ‖z‖) := add_lt_add_right hnorm_lt _
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htemp
  have hzph_le : ‖z + h‖ ≤ R' :=
    le_of_lt (lt_of_le_of_lt (norm_add_le _ _) hsum_lt)
  have hzph_mem : (z + h) ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hzph_le
                                                                       
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
                                                           
  have tri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    have := norm_add_le (w - z) z
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                                            
  let t : ℝ := (z + h).re
  have hwz_eq : w - z = (t : ℂ) + Complex.I * z.im - z := by
    simp [w, t, sub_eq_add_neg, add_assoc]
  have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| :=
    abs_horizontal_diff_eq_abs_real z t
  have t_sub_re : t - z.re = h.re := by
    simp [t, Complex.add_re, sub_eq_add_neg, add_assoc]
  have hwz_abs2 : ‖w - z‖ = |h.re| := by
    simpa [hwz_eq, t_sub_re] using eq_transform
  have hwz_le : ‖w - z‖ ≤ ‖h‖ := by
    simpa [hwz_abs2] using (Complex.abs_re_le_norm h)
  have hw_le'' : ‖w‖ ≤ ‖h‖ + ‖z‖ := by
    exact le_trans tri (add_le_add_left hwz_le _)
  have hw_lt : ‖w‖ < R' := by
    have : ‖h‖ + ‖z‖ < R' := by simpa [add_comm] using hsum_lt
    exact lt_of_le_of_lt hw_le'' this
  have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [w, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using (le_of_lt hw_lt)
  exact And.intro hzph_mem hw_mem

lemma limit_of_Err_ratio_is_zero
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
                                                 
  set g : ℂ → ℂ := fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h
                               
  have hS : Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) :=
    limit_of_S_is_zero (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz
                                        
  have h_upper : Tendsto (fun h => |(2 : ℝ) * S_max z h f|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun x : ℝ => |(2 : ℝ) * x| :=
      (continuous_const.mul continuous_id).abs
    have h0 := hcont.tendsto (0 : ℝ)
    simpa only [Function.comp_def, mul_zero, abs_zero] using h0.comp hS
                                            
  have h_lower_nonneg : ∀ᶠ h in 𝓝 0, 0 ≤ ‖g h‖ :=
    Filter.Eventually.of_forall (fun _ => by simpa [g] using (norm_nonneg (g _)))
                                                                      
  let δ : ℝ := (R - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
    simpa [δ] using half_pos this
  let R' : ℝ := r1 + δ
  have hR'_pos : 0 < R' := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R'] using this
  have hR'_lt_R : R' < R := by
    have hδlt : δ < R - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R))
    have : r1 + δ < r1 + (R - r1) := add_lt_add_right hδlt r1
    simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                 
  have hz_le_r1 : ‖z‖ ≤ r1 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hr1_le_R' : r1 ≤ R' := by
      have : 0 ≤ δ := le_of_lt hδ_pos
      simpa [R'] using (le_add_of_nonneg_right this : r1 ≤ r1 + δ)
    have : ‖z‖ ≤ R' := le_trans hz_le_r1 hr1_le_R'
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                                                                      
  have h_event : ∀ᶠ h in 𝓝 0, ‖g h‖ ≤ |(2 : ℝ) * S_max z h f| := by
                                                                                          
    have hcorner := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') (hz := by
                                                    
      have : ‖z‖ ≤ r1 := hz_le_r1
      exact lt_of_le_of_lt this (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos)))
    refine hcorner.mono ?_
    intro h hh
    have hzh' : z + h ∈ Metric.closedBall (0 : ℂ) R' := hh.1
    have hw' : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) R' := hh.2
    by_cases hh0 : h = 0
    · have : 0 ≤ |(2 : ℝ) * S_max z h f| := abs_nonneg _
      simp [g, hh0, div_zero, norm_zero]
    ·                                        
      have hb :=
        bound_on_Err_ratio (r1:=R') (R:=R) (R0:=R0)
          hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (h:=h) hz' hzh' hw' hh0
      have hb' : ‖g h‖ ≤ 2 * S_max z h f := by
        simpa [g, norm, Err] using hb
      exact le_trans hb' (le_abs_self ((2 : ℝ) * S_max z h f))
                                      
  have h_norm_tendsto : Tendsto (fun h => ‖g h‖) (𝓝 0) (𝓝 0) := by
    refine Filter.Tendsto.squeeze' tendsto_const_nhds h_upper h_lower_nonneg h_event
                                                         
  have h_dist_tendsto : Tendsto (fun h => dist (g h) 0) (𝓝 0) (𝓝 0) := by
    simpa [dist_eq_norm] using h_norm_tendsto
  simpa [g] using (tendsto_iff_dist_tendsto_zero).2 h_dist_tendsto

open _root_.Classical
                                                                                      

lemma If_ext_eq_taxicab_of_mem {r1 R R0 : ℝ} (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) r1) :
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
      = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
  classical
  simp [If_ext, hw]

lemma If_taxicab_param_invariance {r1₁ r1₂ R R0 : ℝ}
    (hr1₁_pos : 0 < r1₁) (hr1₁_lt_R : r1₁ < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (hr1₂_pos : 0 < r1₂) (hr1₂_lt_R : r1₂ < R)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ}
    (hw₁ : w ∈ Metric.closedBall (0 : ℂ) r1₁)
    (hw₂ : w ∈ Metric.closedBall (0 : ℂ) r1₂) :
    If_taxicab hr1₁_pos hr1₁_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₁⟩
    = If_taxicab hr1₂_pos hr1₂_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₂⟩ := by

  simp [If_taxicab]


lemma eventually_decomposition_for_ext
  {R' R R0 : ℝ} (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  (z : ℂ) (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
    g (z + h) - g z = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
                                                                             
  have h_event := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') hz
  refine h_event.mono ?_
  intro h hh
             
  let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
                                                        
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                                           
  have hgzh : g (z + h)
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z + h) hh.1
  have hgz : g z
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z) hz'
                                                              
  have H :=
    If_diff_decomposition_final (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one (f:=f) (hf:=hf)
      (z:=z) (h:=h)
      (hz:=hz') (hzh:=hh.1) (hw:=hh.2)
                                               
  calc
    g (z + h) - g z
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩
          - If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
            simp [hgzh, hgz]
    _ = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
      simpa using H

lemma tendsto_Err_ratio_radius (R' R R0 : ℝ) (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z : ℂ} (hz : ‖z‖ < R') :
  Tendsto (fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
                                               
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                 
  simpa using
    (limit_of_Err_ratio_is_zero (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (hz:=hz'))



lemma hasDerivWithinAt_congr_eqOn {f g : ℂ → ℂ} {s : Set ℂ} {z f' : ℂ}
  (hEq : Set.EqOn f g s) (hz : z ∈ s) :
  HasDerivWithinAt g f' s z → HasDerivWithinAt f f' s z := by
  intro hg
  have hfg : ∀ x ∈ s, f x = g x := fun x hx => hEq hx
  simpa using (HasDerivWithinAt.congr_of_mem (h := hg) (hs := hfg) (hx := hz))

lemma differentiableOn_of_hasDerivWithinAt {f : ℂ → ℂ} {s : Set ℂ} {F : ℂ → ℂ}
  (h : ∀ z ∈ s, HasDerivWithinAt f (F z) s z) : DifferentiableOn ℂ f s := by
  intro z hz
  exact (h z hz).differentiableWithinAt

lemma If_ext_agree_on_smallBall {r1 R' R R0 : ℝ}
  (hr1_pos : 0 < r1) (hR'_pos : 0 < R') (hr1_lt_R : r1 < R) (hR'_lt_R : R' < R) (hr1_lt_R' : r1 < R') (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
  Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
           (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
           (Metric.closedBall (0 : ℂ) r1) := by
  intro w hw
                                                                                
  have hw' : w ∈ Metric.closedBall (0 : ℂ) R' :=
    mem_closedBall_mono_radius (z:=w) (r:=r1) (R:=R') hw (le_of_lt hr1_lt_R')
                                                                  
  have hleft :
      If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=r1) (R:=R) (R0:=R0)
        hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw)
  have hright :
      If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0)
        hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw')
                                           
  have hparam :=
    If_taxicab_param_invariance (r1₁:=r1) (r1₂:=R') (R:=R) (R0:=R0)
      hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hR'_pos hR'_lt_R hf (w:=w) hw hw'
                     
  calc
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := hleft
    _ = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := hparam
    _ = If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w := by
          simpa using hright.symm

lemma hasDerivAt_of_local_decomposition' (g : ℂ → ℂ) (z F : ℂ)
  (Err_func : ℂ → ℂ)
  (hdecomp : ∀ᶠ h in 𝓝 (0:ℂ), g (z + h) - g z = F * h + Err_func h)
  (hErr : Tendsto (fun h => Err_func h / h) (𝓝 (0:ℂ)) (𝓝 (0:ℂ))) :
  HasDerivAt g F z := by
                                                             
  have hdecomp_within : ∀ᶠ h in 𝓝[≠] (0:ℂ), g (z + h) - g z = F * h + Err_func h :=
    (hdecomp.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ)))
                                                                 
  have h_ne0 : ∀ᶠ h in 𝓝[≠] (0:ℂ), h ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℂ)) (s := ({0}ᶜ : Set ℂ))] with h hh
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
                                                   
  have h_eq_slope : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      h⁻¹ • (g (z + h) - g z) = F + Err_func h / h := by
    refine (hdecomp_within.and h_ne0).mono ?_
    intro h hh
    rcases hh with ⟨hEq, hne⟩
                                                   
    have H0 : h⁻¹ • (g (z + h) - g z) = h⁻¹ • (F * h + Err_func h) := by
      simpa using congrArg (fun x => h⁻¹ • x) hEq
                                     
    have h1 : h⁻¹ * (F * h) = F := by
      have hne' : h ≠ 0 := hne
      calc
        h⁻¹ * (F * h) = F * (h⁻¹ * h) := by
          ac_rfl
        _ = F * 1 := by simp [hne']
        _ = F := by simp
    have h2 : h⁻¹ * Err_func h = Err_func h / h := by
      simp [div_eq_mul_inv, mul_comm]
    calc
      h⁻¹ • (g (z + h) - g z)
          = h⁻¹ • (F * h + Err_func h) := H0
      _ = h⁻¹ * (F * h + Err_func h) := by simp [smul_eq_mul]
      _ = h⁻¹ * (F * h) + h⁻¹ * (Err_func h) := by simp [mul_add]
      _ = F + Err_func h / h := by simp [h1, h2]
                                        
  have hErr_within : Tendsto (fun h => Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) :=
    hErr.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
  have h_const : Tendsto (fun _ : ℂ => F) (𝓝[≠] (0:ℂ)) (𝓝 F) := tendsto_const_nhds
  have h_sum : Tendsto (fun h => F + Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (F + 0)) :=
    h_const.add hErr_within
  have h_target : Tendsto (fun h => h⁻¹ • (g (z + h) - g z)) (𝓝[≠] (0:ℂ)) (𝓝 F) := by
    have := (Filter.tendsto_congr' h_eq_slope).2 h_sum
    simpa [zero_add] using this
                                                             
  exact (hasDerivAt_iff_tendsto_slope_zero).2 h_target

lemma uniqueDiffWithinAt_convex_complex {s : Set ℂ} (hconv : Convex ℝ s)
    (hs : (interior s).Nonempty) {x : ℂ} (hx : x ∈ closure s) :
    UniqueDiffWithinAt ℂ s x := by
                                                                   
  have hR : UniqueDiffWithinAt ℝ s x :=
    uniqueDiffWithinAt_convex (E := ℂ) (conv := hconv) (hs := hs) (x := x) (hx := hx)
                                                       
  have dR : Dense ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ) := by
    simpa using (hR.dense_tangentConeAt)
                                                                  
  have h_tc_subset : tangentConeAt ℝ s x ⊆ tangentConeAt ℂ s x :=
    tangentConeAt_mono_field
                                                                             
  set TC : Set ℂ := tangentConeAt ℂ s x
  set Sℂ : Submodule ℂ ℂ := Submodule.span ℂ TC
  set Sℝ : Submodule ℝ ℂ := Sℂ.restrictScalars ℝ
  have h_span_le : (Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) ≤ Sℝ := by
                                                   
    refine Submodule.span_le.mpr ?_
    intro v hv
    have hv' : v ∈ TC := h_tc_subset hv
    have : v ∈ Sℂ := Submodule.subset_span hv'
    simpa [Sℝ] using this
                                                                            
  have hsubset_sets :
      ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ)
        ⊆ ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := by
    intro z hz
    have hz' : z ∈ Sℝ := h_span_le hz
    simpa [Sℝ] using hz'
  have dC : Dense ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := dR.mono hsubset_sets
                                 
  exact ⟨dC, hx⟩

lemma interior_closedBall_nonempty_of_pos {R : ℝ} (hR_pos : 0 < R) :
    (interior (Metric.closedBall (0 : ℂ) R)).Nonempty := by
                                                               
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hR_pos
                                                                  
  have hsub : Metric.ball (0 : ℂ) R ⊆ interior (Metric.closedBall (0 : ℂ) R) :=
    Metric.ball_subset_interior_closedBall
                                   
  exact ⟨0, hsub h0mem⟩

lemma mem_closure_of_mem_closedBall {R : ℝ} {z : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  z ∈ closure (Metric.closedBall (0 : ℂ) R) := by
  exact subset_closure hz

lemma uniqueDiffWithinAt_closedBall_complex_of_mem {R : ℝ} {z : ℂ}
  (hR_pos : 0 < R) (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) R) z :=
by
                              
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) R) :=
    convex_closedBall (0 : ℂ) R
                                         
  have hnonempty : (interior (Metric.closedBall (0 : ℂ) R)).Nonempty :=
    interior_closedBall_nonempty_of_pos (R := R) hR_pos
                                                
  have hz_cl : z ∈ closure (Metric.closedBall (0 : ℂ) R) :=
    mem_closure_of_mem_closedBall (R := R) (z := z) hz
                                              
  exact uniqueDiffWithinAt_convex_complex hconv hnonempty hz_cl

lemma If_is_differentiable_on
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    DifferentiableOn ℂ (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1)
    ∧
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      derivWithin (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1) z = f z := by
  set s : Set ℂ := Metric.closedBall (0 : ℂ) r1
  have hHasDerivWithinAt : ∀ z ∈ s,
      HasDerivWithinAt (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (f z) s z := by
    intro z hz
                                                        
    let δ : ℝ := (R - r1) / 2
    have hδ_pos : 0 < δ := by
      have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
      simpa [δ] using half_pos this
    let R' : ℝ := r1 + δ
    have hR'_pos : 0 < R' := by
      have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
      simpa [R'] using this
    have hR'_lt_R : R' < R := by
      have hδlt : δ < R - r1 := by
        have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
        simpa [δ] using (half_lt_self this)
      have : r1 + δ < r1 + (R - r1) := add_lt_add_right hδlt r1
      simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hr1_lt_R' : r1 < R' := by
      have : r1 < r1 + δ := by simpa [add_comm, add_left_comm, add_assoc, R', δ] using (lt_of_le_of_lt (le_of_eq rfl) (add_lt_add_right hδ_pos r1))
      simpa [R'] using this
                                       
    have hz_le_r1 : ‖z‖ ≤ r1 := by
      simpa [s, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
    have hz_lt_R' : ‖z‖ < R' := lt_of_le_of_lt hz_le_r1 (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos))
                                             
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
                                         
    have hdecomp := eventually_decomposition_for_ext (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf z hz_lt_R'
                                
    have hErr := tendsto_Err_ratio_radius (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf hz_lt_R'
                                                                
    have hDerivAt_g : HasDerivAt g (f z) z :=
      hasDerivAt_of_local_decomposition' (g := g) (z := z) (F := f z)
        (Err_func := fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h)
        (hdecomp := by
                                                                                          
          simpa [g] using hdecomp)
        (hErr := by
                                                                         
          simpa using hErr)
                                               
    have hWithin_g : HasDerivWithinAt g (f z) s z := hDerivAt_g.hasDerivWithinAt
                                                      
    have hEq : Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
                        (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
                        s :=
      If_ext_agree_on_smallBall (r1:=r1) (R':=R') (R:=R) (R0:=R0)
        hr1_pos hR'_pos hr1_lt_R hR'_lt_R hr1_lt_R' hR_lt_R0 hR0_lt_one hf
                                                  
    exact hasDerivWithinAt_congr_eqOn (f := If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
      (g := g) (s := s) (z := z) (f' := f z) hEq hz hWithin_g
                                 
  refine And.intro ?hdiff ?hderiv
  ·                                                                            
    apply differentiableOn_of_hasDerivWithinAt
    intro z hz
    exact hHasDerivWithinAt z hz
  ·                                   
    intro z hz
    have hUD : UniqueDiffWithinAt ℂ s z :=
      uniqueDiffWithinAt_closedBall_complex_of_mem (R := r1) hr1_pos (z := z) (hz := by simpa [s] using hz)
    have hD := hHasDerivWithinAt z hz
    simpa using hD.derivWithin hUD

open scoped _root_.Topology

theorem AnalyticOnNhd.mono_closedBall {B : ℂ → ℂ} {R : ℝ} (R' : ℝ)
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall 0 R)) (hR' : R' < R) :
    AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by

  exact hB.mono (Metric.closedBall_subset_closedBall (le_of_lt hR'))


lemma I_is_antiderivative
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J : ℂ → ℂ, AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) ∧
      J 0 = 0 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z := by
  classical
                                           
  have hB_on_R' : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.mono_closedBall R' hB hR'_lt_R
  have hderiv_on_R' : AnalyticOnNhd ℂ (deriv B) (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.deriv hB_on_R'
  let L : ℂ → ℂ := fun z => deriv B z / B z
  have hL_on_R' : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) R') := by
    simpa [L] using AnalyticOnNhd.div hderiv_on_R' hB_on_R' hB_ne_zero
                                      
  let δ : ℝ := (R' - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R' - r1 := sub_pos.mpr hr1_lt_R'
    simpa [δ] using half_pos this
  let R_mid : ℝ := r1 + δ
  have hR_mid_pos : 0 < R_mid := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R_mid] using this
  have hr1_lt_R_mid : r1 < R_mid := by
    have : 0 < δ := hδ_pos
    simpa [R_mid] using (lt_add_of_pos_right r1 this)
  have hR_mid_lt_R' : R_mid < R' := by
    have hδlt : δ < R' - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R'))
    have : r1 + δ < r1 + (R' - r1) := add_lt_add_right hδlt r1
    simpa [R_mid, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                                                        
  let J : ℂ → ℂ :=
    If_ext (r1 := R_mid) (R := R') (R0 := R) hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one L hL_on_R'

  have hIf :=
    (If_is_differentiable_on (r1 := R_mid) (R := R') (R0 := R)
      hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one (f := L) hL_on_R')
  have hDiffOn_mid : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) R_mid) := by
    simpa [J] using hIf.1
                                                         
  have hDiffOn_ball_R_mid : DifferentiableOn ℂ J (Metric.ball (0 : ℂ) R_mid) :=
    hDiffOn_mid.mono Metric.ball_subset_closedBall
                                                                       
  have hJ_analyticOnNhd : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) := by
    intro z hz
                                                               
    have hz_le : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
                                                                                
    exact (DifferentiableOn.analyticAt (s := Metric.ball (0 : ℂ) R_mid)
      (f := J) hDiffOn_ball_R_mid (Metric.isOpen_ball.mem_nhds hz_ball))
                
  have h0_in_mid : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R_mid := by
    simpa [Metric.mem_closedBall, dist_self] using (le_of_lt hR_mid_pos)
  have hJ0 : J 0 = 0 := by
    simp [J, If_ext, If_taxicab, h0_in_mid]
                                                           
  have hderiv_eq : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = L z := by
    intro z hz
                                        
    have hz_le : dist z (0 : ℂ) ≤ r1 := by simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
    have hz_cb_mid : z ∈ Metric.closedBall (0 : ℂ) R_mid := Metric.ball_subset_closedBall hz_ball
                                                                                      
    have h_cb_nhds : Metric.closedBall (0 : ℂ) R_mid ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz_ball) Metric.ball_subset_closedBall
                                                                                     
    have hDW_eq_L : derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z = L z := by
      simpa [J] using hIf.2 z hz_cb_mid
                                                                                                    
    have hHasWithin : HasDerivWithinAt J (derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z)
        (Metric.closedBall (0 : ℂ) R_mid) z :=
      (hDiffOn_mid z hz_cb_mid).hasDerivWithinAt
    have hHasWithinL : HasDerivWithinAt J (L z) (Metric.closedBall (0 : ℂ) R_mid) z := by
      simpa [hDW_eq_L]
        using hHasWithin
                                                                           
    have hHasDerivAt : HasDerivAt J (L z) z :=
      HasDerivWithinAt.hasDerivAt hHasWithinL h_cb_nhds
                                           
    simpa using hHasDerivAt.deriv
                       
  refine ⟨J, hJ_analyticOnNhd, hJ0, ?_⟩
  intro z hz
  simpa [L] using hderiv_eq z hz



lemma H_at_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 1 / B 0 := by
  simp [H_auxiliary, hJ_zero]

lemma log_deriv_id
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z = deriv B z := by
  intro z hz
                                                   
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR'_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR'_le
    simpa using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hJd := hJ_deriv z hz
  have hmult := congrArg (fun t => t * B z) hJd
  have hR2 : (deriv B z / B z) * B z = deriv B z * B z / B z := by
    simpa using (div_mul_eq_mul_div (deriv B z) (B z) (B z))
  have hmult' : deriv J z * B z = deriv B z * B z / B z := by
    simpa [hR2] using hmult
  have hdiv' : deriv B z * B z / B z = deriv B z := by
    field_simp [hBnz]
  calc
    deriv J z * B z = deriv B z * B z / B z := hmult'
    _ = deriv B z := by simpa using hdiv'

lemma log_deriv_identity
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z - deriv B z = 0 := by
  intro z hz
  have h_eq := log_deriv_id hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  rw [h_eq]
  simp

lemma H_derivative_quotient_rule
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv (fun w => Complex.exp (J w)) z * B z - deriv B z * Complex.exp (J z)) / (B z)^2 := by
  intro z hz
                                        
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa using hzR''
                                                      
  have hB_nz : B z ≠ 0 := hB_ne_zero z hzR
  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
    apply AnalyticOnNhd.mono_closedBall R' hB
    assumption
  have hB_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hF_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z := hJ_diff.cexp
                                            
  have h := deriv_div (hc := hF_diff) (hd := hB_diff) (hx := hB_nz)
  unfold H_auxiliary
  simpa only [Pi.div_def, mul_comm] using h

lemma exp_I_derivative_chain_rule
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (fun w => Complex.exp (J w)) z = deriv J z * Complex.exp (J z) := by
  intro z hz
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hJ_has : HasDerivAt J (deriv J z) z := hJ_diff.hasDerivAt
  have hcomp := (Complex.hasDerivAt_exp (J z)).comp z hJ_has
                           
  simpa only [Function.comp_def, mul_comm] using hcomp.deriv

lemma H_derivative_calc
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv J z * B z - deriv B z) * Complex.exp (J z) / (B z)^2 := by
  intro z hz
                                 
  have hquot := H_derivative_quotient_rule hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                            
  have hchain := exp_I_derivative_chain_rule hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                             
  rw [hquot, hchain]

  have h1 : deriv J z * Complex.exp (J z) * B z - deriv B z * Complex.exp (J z) =
           Complex.exp (J z) * (deriv J z * B z - deriv B z) := by ring
  rw [h1]

  ring

lemma H_derivative_is_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  intro z hz
  have hcalc :=
    H_derivative_calc hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  have hident :=
    log_deriv_identity hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  simpa [hident] using hcalc

lemma zero_mem_closedBall_zero_radius {r1 : ℝ} (hr1 : 0 ≤ r1) : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using hr1

lemma H_deriv_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  simpa using
    (H_derivative_is_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv)

lemma H_auxiliary_differentiableOn_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
by
                                              
  have hsubset : Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    have hz' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hle : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    have : dist z (0 : ℂ) ≤ R := le_trans hz' hle
    simpa [Metric.mem_closedBall] using this
                                                    
  have hJ_diff : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) r1) :=
    hJ.differentiableOn
  have hB_diff_r1 : DifferentiableOn ℂ B (Metric.closedBall (0 : ℂ) r1) :=
    (hB.differentiableOn).mono hsubset
                                                         
  have hExp_diff : DifferentiableOn ℂ Complex.exp (Set.univ : Set ℂ) :=
    (Complex.differentiable_exp.differentiableOn)
  have hExp_comp : DifferentiableOn ℂ (fun z => Complex.exp (J z)) (Metric.closedBall (0 : ℂ) r1) := by
    refine hExp_diff.comp hJ_diff ?_
    intro x hx; simp
                                                 
  have hB_ne_zero_r1 : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z ≠ 0 := by
    intro z hz; exact hB_ne_zero z (by
    have x : Metric.closedBall 0 r1 ⊆ Metric.closedBall 0 R' := Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R')
    simp
    simp at hz
    linarith
    )
                                                
  have hdiv : DifferentiableOn ℂ (fun z => Complex.exp (J z) / B z)
      (Metric.closedBall (0 : ℂ) r1) :=
    hExp_comp.div hB_diff_r1 hB_ne_zero_r1
                                     
  unfold H_auxiliary
  exact hdiv

lemma hasDerivAt_H_auxiliary_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0 z := by
  intro z hz
                                               
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa [Metric.mem_closedBall] using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z (hzR)
                                               
  have hJ_anal : AnalyticAt ℂ J z := hJ z hz
  have hExp_diff_at_Jz : DifferentiableAt ℂ Complex.exp (J z) :=
    Complex.differentiableAt_exp
  have hc_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z :=
    hExp_diff_at_Jz.comp z hJ_anal.differentiableAt

  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
    apply AnalyticOnNhd.mono_closedBall R' hB
    assumption
  have hd_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
                                                                      
  have hH_diff : DifferentiableAt ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z := by
    unfold H_auxiliary
    convert (preTransparency := .instances) hc_diff.div hd_diff hBnz using 1
  have hH_has : HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z) z :=
    hH_diff.hasDerivAt
  have hderiv0 : deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 :=
    H_deriv_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  simpa [hderiv0] using hH_has

lemma fderivWithin_eq_zero_of_derivWithin_eq_zero {s : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (_hdiff : DifferentiableWithinAt ℂ f s x)
    (hderiv : derivWithin f s x = 0) :
    fderivWithin ℂ f s x = 0 := by
  rw [← toSpanSingleton_derivWithin, hderiv]
  simp

lemma hasDerivWithinAt_of_hasDerivAt {f : ℂ → ℂ} {s : Set ℂ} {x : ℂ}
    (h : HasDerivAt f 0 x) : HasDerivWithinAt f 0 s x := by
  simpa using h.hasDerivWithinAt


lemma H_auxiliary_fderivWithin_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 :=
by
  intro z hz
                                                                                   
  have hHasAt :=
    hasDerivAt_H_auxiliary_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero
      hJ hJ_zero hJ_deriv z hz
  have hHasWithin :
      HasDerivWithinAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0
        (Metric.closedBall (0 : ℂ) r1) z :=
    hasDerivWithinAt_of_hasDerivAt hHasAt
                                         
  have hdiff : DifferentiableWithinAt ℂ
      (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) z :=
    hHasWithin.differentiableWithinAt
                                                                            
  classical
  have hderivWithin0 :
      derivWithin (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 := by
    by_cases hUDc : UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) r1) z
    · simpa using hHasWithin.derivWithin hUDc
    · simpa using
        (derivWithin_zero_of_not_uniqueDiffWithinAt
          (𝕜 := ℂ)
          (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (s := Metric.closedBall (0 : ℂ) r1) (x := z) hUDc)
                                              
  exact fderivWithin_eq_zero_of_derivWithin_eq_zero hdiff hderivWithin0

lemma H_is_constant
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z =
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 := by
  intro z hz
                              
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) r1) := by
    simpa using (convex_closedBall (0 : ℂ) r1)
                                              
  have hdiff : DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
    H_auxiliary_differentiableOn_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ
                                            
  have hfderiv0 : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) x = 0 :=
    H_auxiliary_fderivWithin_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
                                 
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 :=
    zero_mem_closedBall_zero_radius (le_of_lt hr1_pos)
                                           
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      ‖fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (Metric.closedBall (0 : ℂ) r1) x‖ ≤ 0 := by
    intro x hx
    simp [hfderiv0 x hx]
  have hineq :=
    Convex.norm_image_sub_le_of_norm_fderivWithin_le (𝕜 := ℂ)
      (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (s := Metric.closedBall (0 : ℂ) r1) (x := (0 : ℂ)) (y := z)
      hdiff hbound hs h0mem hz
  have hzero : H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z -
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 0 := by
    have : ‖H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z -
        H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0‖ ≤ 0 := by
      simpa using hineq
    simpa [norm_le_zero_iff] using this
  simpa [sub_eq_add_neg] using sub_eq_zero.mp hzero

lemma H_is_one
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z = 1 / B 0 := by
  intro z hz
  have hconst := H_is_constant hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  have h0 := H_at_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
  simpa [h0] using hconst

lemma analytic_log_exists
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z = B 0 * Complex.exp (J z) := by
  intro z hz
                                             
  have hH_const := H_is_one hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                         
  unfold H_auxiliary at hH_const
                                          
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    exact le_trans hzR' (by linarith)
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hR_pos : 0 < R := lt_trans (lt_trans hr1_pos hr1_lt_R') hR'_lt_R
  have hB0nz : B 0 ≠ 0 := hB_ne_zero 0 (by
    simp [Metric.closedBall, dist_zero_right]
    exact le_of_lt (by linarith))
                                                  
  have heq : Complex.exp (J z) * B 0 = B z := by
    field_simp [hBnz, hB0nz] at hH_const
    exact hH_const
                                              
  rw [← heq, mul_comm]

lemma modulus_of_exp_I
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (Complex.exp (J z)) = Real.exp (Complex.re (J z)) := by
  intro z hz
  exact Complex.norm_exp (J z)

lemma modulus_of_B_product_form
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * norm (Complex.exp (J z)) := by
  intro z hz
  have hBform := analytic_log_exists hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                          
  simpa [norm_mul] using (congrArg norm hBform)

lemma modulus_of_exp_log
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * Real.exp (Complex.re (J z)) := by
  intro z hz
  rw [modulus_of_B_product_form hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]
  rw [modulus_of_exp_I hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]

lemma log_modulus_as_sum
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) =
      Real.log (norm (B 0)) + Real.log (Real.exp (Complex.re (J z))) := by
  intro z hz
                                                     
  have h_eq := modulus_of_exp_log hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                                         
  rw [h_eq, Real.log_mul]
  ·                       
                                                                            
    simp
    apply hB_ne_zero
                                           
    rw [Metric.mem_closedBall, dist_self]
    linarith
  ·                                        
    exact Real.exp_ne_zero _

lemma real_log_of_modulus_difference
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J z) := by
  intro z hz
                                     
  have h_sum := log_modulus_as_sum hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                    
  rw [h_sum]
                                                                       
  rw [Real.log_exp]
  ring

theorem log_of_analytic
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.closedBall (0 : ℂ) r1) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  have hB_ne_zero_R' : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0 := hB_ne_zero
  obtain ⟨J_B, hJ, hJ0, hJderiv⟩ :=
    I_is_antiderivative hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero_R'
  refine ⟨J_B, hJ, hJ0, hJderiv, ?_⟩
  intro z hz
  simpa using
    (real_log_of_modulus_difference hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ0 hJderiv z hz)

end Erdos970

end

theorem solution : type_of% @Erdos970.log_of_analytic := @Erdos970.log_of_analytic
