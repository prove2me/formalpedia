-- Prove2me | solution 2 for CohnElkies.complexFrullaniKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:17.224014+00:00
-- url     : https://prove2.me/submissions/83ed37d7-faa0-4d48-9581-ec8b7d8e7c7e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
theorem h47_laplace (z w : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1,
      (w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))) =
      complexFrullaniKernel z w x := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have h0 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := fun s => by
    simpa using (hasDerivAt_id s).ofReal_comp
  have hd : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => -Complex.exp (-complexFrullaniSegment z w s * (x : ℂ)) / (x : ℂ))
      ((w - z) * Complex.exp (-complexFrullaniSegment z w s * (x : ℂ))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -complexFrullaniSegment z w s * (x : ℂ))
        (-(w - z) * x) s := by
      have := (((h0 s).mul_const (w - z)).const_add z).neg.mul_const (x : ℂ)
      unfold complexFrullaniSegment
      exact this.congr_deriv (by ring)
    have h2 := (h1.cexp.neg).div_const (x : ℂ)
    exact h2.congr_deriv (by rw [div_eq_iff hx']; ring)
  have hc : Continuous (fun s : ℝ => (w - z) * Complex.exp (-complexFrullaniSegment z w s * (x : ℂ))) := by
    unfold complexFrullaniSegment; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable _ _)]
  unfold complexFrullaniKernel complexFrullaniSegment
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero]
  rw [show z + (w - z) = w by ring]
  ring

theorem h47_frullani_bound (z w : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖complexFrullaniKernel z w x‖ ≤ ‖w - z‖ * Real.exp (-(min z.re w.re) * x) := by
  rw [← h47_laplace z w hx.ne']
  have key : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖(w - z) * Complex.exp (-complexFrullaniSegment z w t * (x : ℂ))‖ ≤
        ‖w - z‖ * Real.exp (-(min z.re w.re) * x) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.2
    have hre : (-complexFrullaniSegment z w t * (x : ℂ)).re = -(z.re + t * (w.re - z.re)) * x := by
      unfold complexFrullaniSegment; simp; try ring
    rw [hre]
    have hm : min z.re w.re ≤ z.re + t * (w.re - z.re) := by
      rcases le_total z.re w.re with h | h
      · rw [min_eq_left h]; nlinarith [ht.1]
      · rw [min_eq_right h]; nlinarith [ht.2]
    nlinarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const key
  simpa using this

theorem solution
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (complexFrullaniKernel z w) (Ioi 0) := by
  have hm : 0 < min z.re w.re := lt_min hz hw
  have hg : IntegrableOn (fun x : ℝ => ‖w - z‖ * Real.exp (-(min z.re w.re) * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hm).const_mul _
  have hc : ContinuousOn (complexFrullaniKernel z w) (Ioi 0) := by
    unfold complexFrullaniKernel
    exact ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => Complex.ofReal_ne_zero.2 (ne_of_gt hx))
  refine hg.mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
    (MeasureTheory.ae_of_all _ fun x hx => h47_frullani_bound z w hx)

