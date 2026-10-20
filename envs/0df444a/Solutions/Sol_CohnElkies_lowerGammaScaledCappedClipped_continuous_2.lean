-- Prove2me | solution 2 for CohnElkies.lowerGammaScaledCappedClipped_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:56:45.687969+00:00
-- url     : https://prove2.me/submissions/89641ab1-c6f7-43be-a1c0-b5261014c369

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
theorem h47_int_abs_pow_exp (n : ℕ) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0, Real.rpow_natCast]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall
theorem h47c_ne_neg_nat_negI {y : ℝ} (hy : y ≠ 0) :
    ∀ m : ℕ, -Complex.I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.im h
  simp at this
  exact hy this

theorem h47c_ne_neg_nat_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    ∀ m : ℕ, (ℓ : ℂ) + Complex.I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := m.cast_nonneg
  linarith

theorem h47c_contAt_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    ContinuousAt (fun y : ℝ => Real.log ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) y := by
  have hG : ContinuousAt (fun y : ℝ => Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)) y :=
    (Complex.differentiableAt_Gamma _ (h47c_ne_neg_nat_pos hℓ y)).continuousAt.comp
      (f := fun y : ℝ => (ℓ : ℂ) + Complex.I * (y : ℂ) / 2) (by fun_prop)
  exact hG.norm.log (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (h47c_ne_neg_nat_pos hℓ y)))

theorem h47c_contAt_log {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ContinuousAt (lowerGammaBoundaryLog ℓ R) y := by
  have hG : ContinuousAt (fun y : ℝ => Complex.Gamma (-Complex.I * (y : ℂ) / 2)) y :=
    (Complex.differentiableAt_Gamma _ (h47c_ne_neg_nat_negI hy)).continuousAt.comp
      (f := fun y : ℝ => -Complex.I * (y : ℂ) / 2) (by fun_prop)
  have h1 := hG.norm.log (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (h47c_ne_neg_nat_negI hy)))
  have h2 := h47c_contAt_pos hℓ R
  unfold lowerGammaBoundaryLog
  exact (continuousAt_const.add h1).sub (h47c_contAt_pos hℓ y)

theorem h47c_tendsto_log {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    Tendsto (lowerGammaBoundaryLog ℓ R) (𝓝[≠] 0) atTop := by
  -- decomposition for y ≠ 0
  have hdec : ∀ y : ℝ, y ≠ 0 → lowerGammaBoundaryLog ℓ R y =
      (ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2 + 1)‖ -
        Real.log ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) +
      (-Real.log y + Real.log 2) := by
    intro y hy
    have hs : -Complex.I * (y : ℂ) / 2 ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hy this
    have h1 := Complex.Gamma_add_one _ hs
    have hn1 : ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (h47c_ne_neg_nat_negI hy))
    have hns : ‖-Complex.I * (y : ℂ) / 2‖ = |y| / 2 := by simp
    have hlog : Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2 + 1)‖ =
        Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ + Real.log y - Real.log 2 := by
      rw [h1, norm_mul, hns, Real.log_mul (by positivity) hn1, Real.log_div (by positivity) two_ne_zero,
        Real.log_abs]
      ring
    unfold lowerGammaBoundaryLog
    rw [hlog]; ring
  have hc1 : ContinuousAt (fun y : ℝ => Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2 + 1)‖) 0 := by
    have hne : ∀ m : ℕ, -Complex.I * ((0:ℝ) : ℂ) / 2 + 1 ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ m := m.cast_nonneg
      linarith
    have hG : ContinuousAt (fun y : ℝ => Complex.Gamma (-Complex.I * (y : ℂ) / 2 + 1)) 0 :=
      (Complex.differentiableAt_Gamma _ hne).continuousAt.comp
        (f := fun y : ℝ => -Complex.I * (y : ℂ) / 2 + 1) (by fun_prop)
    exact hG.norm.log (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero hne))
  have hcont : ContinuousAt (fun y : ℝ => ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2 + 1)‖ -
        Real.log ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) 0 :=
    (continuousAt_const.add hc1).sub (h47c_contAt_pos hℓ 0)
  have hA := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ)))
  have hB : Tendsto (fun y : ℝ => -Real.log y + Real.log 2) (𝓝[≠] 0) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero)
  have hsum := hA.add_atTop hB
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hdec y hy).symm
theorem h47c_capped_cont {ℓ : ℝ} (hℓ : 0 < ℓ) (R D : ℝ) : Continuous (lowerGammaBoundaryCapped ℓ R D) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    rw [← continuousWithinAt_compl_self]
    have hev : ∀ᶠ y in 𝓝[≠] (0:ℝ), lowerGammaBoundaryCapped ℓ R D y = D := by
      filter_upwards [self_mem_nhdsWithin, (h47c_tendsto_log hℓ R).eventually_ge_atTop D] with y hy0 hyD
      unfold lowerGammaBoundaryCapped
      rw [if_neg (by simpa using hy0), min_eq_right hyD]
    have h0 : lowerGammaBoundaryCapped ℓ R D 0 = D := by unfold lowerGammaBoundaryCapped; simp
    unfold ContinuousWithinAt
    rw [h0]
    exact tendsto_const_nhds.congr' (hev.mono fun y h => h.symm)
  · have hev : (fun y => min (lowerGammaBoundaryLog ℓ R y) D) =ᶠ[𝓝 y] lowerGammaBoundaryCapped ℓ R D := by
      filter_upwards [isOpen_ne.mem_nhds hy] with z hz
      unfold lowerGammaBoundaryCapped
      rw [if_neg hz]
    have hc : ContinuousAt (fun y => min (lowerGammaBoundaryLog ℓ R y) D) y :=
      (h47c_contAt_log hℓ R hy).min continuousAt_const
    exact hc.congr_of_eventuallyEq hev.symm

theorem solution
    {d : ℕ} (hd : 0 < d) (c D n : ℝ) :
    Continuous (lowerGammaScaledCappedClipped d c D n) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hℓ : (0:ℝ) < (d : ℝ) / 2 := by positivity
  unfold lowerGammaScaledCappedClipped
  exact (((h47c_capped_cont hℓ _ D).comp (continuous_const.mul continuous_id)).add continuous_const).max
    continuous_const

