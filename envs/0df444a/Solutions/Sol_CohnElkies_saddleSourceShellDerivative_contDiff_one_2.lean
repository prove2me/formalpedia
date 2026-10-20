-- Prove2me | solution 2 for CohnElkies.saddleSourceShellDerivative_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:52:30.988348+00:00
-- url     : https://prove2.me/submissions/a429dacd-65ec-4bea-9104-d58f21111e82

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
theorem h47_param_sinh_C1 {G : ℝ → ℝ} (hG : Continuous G) (a b : ℝ) :
    ContDiff ℝ 1 (fun u : ℝ => ∫ t in a..b, G t * Real.sinh (u * t)) := by
  have hderiv : ∀ u₀ : ℝ, HasDerivAt (fun u : ℝ => ∫ t in a..b, G t * Real.sinh (u * t))
      (∫ t in a..b, G t * (t * Real.cosh (u₀ * t))) u₀ := by
    intro u₀
    have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := a) (b := b)
      (F := fun u t => G t * Real.sinh (u * t)) (F' := fun u t => G t * (t * Real.cosh (u * t)))
      (x₀ := u₀) (bound := fun t => |G t| * (|t| * Real.cosh ((|u₀| + 1) * |t|)))
      (Metric.ball_mem_nhds u₀ one_pos)
      (Filter.Eventually.of_forall fun u => (hG.mul (Real.continuous_sinh.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable)
      ((hG.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
      ((hG.mul (continuous_id.mul (Real.continuous_cosh.comp
        (continuous_const.mul continuous_id)))).aestronglyMeasurable)
      (MeasureTheory.ae_of_all _ fun t _ u hu => by
        have hu' : |u| ≤ |u₀| + 1 := by
          have h1 : |u - u₀| < 1 := by rw [← Real.dist_eq]; exact Metric.mem_ball.mp hu
          have := abs_sub_abs_le_abs_sub u u₀
          linarith
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _)]
        gcongr
        rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ |u₀| + 1)]
        exact mul_le_mul_of_nonneg_right hu' (abs_nonneg t))
      ((hG.abs.mul (continuous_abs.mul (Real.continuous_cosh.comp
        (continuous_const.mul continuous_abs)))).intervalIntegrable _ _)
      (MeasureTheory.ae_of_all _ fun t _ u _ => by
        have := (((hasDerivAt_id u).mul_const t).sinh).const_mul (G t)
        refine this.congr_deriv ?_
        simp only [id_eq, one_mul]
        ring)
    exact h.2
  rw [contDiff_one_iff_deriv]
  refine ⟨fun u => (hderiv u).differentiableAt, ?_⟩
  have hD : deriv (fun u : ℝ => ∫ t in a..b, G t * Real.sinh (u * t)) =
      fun u => ∫ t in a..b, G t * (t * Real.cosh (u * t)) := funext fun u => (hderiv u).deriv
  rw [hD]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hG.comp continuous_snd).mul (continuous_snd.mul (Real.continuous_cosh.comp
    (continuous_fst.mul continuous_snd)))

theorem solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ (1 : WithTop ℕ∞)
      (saddleSourceShellDerivative ε) := by
  have hc : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  set c := shortCutoff ε
  set E := shortEndpoint ε
  have hm : Continuous (fun a : ℝ => max a c) := continuous_id.max continuous_const
  have hG1 : Continuous (fun a : ℝ => shortShellDensity ε (max a c) * max a c) := by
    refine Continuous.mul ?_ hm
    unfold shortShellDensity shortMargin
    refine Continuous.neg (Continuous.div ?_ ?_ ?_)
    · exact (continuous_const.sub (continuous_const.mul (continuous_const.add hm))).mul
        (Real.continuous_exp.comp (continuous_const.mul hm))
    · exact (continuous_const.mul (hm.pow 2)).mul (Real.continuous_cosh.comp hm)
    · intro a
      have h1 : 0 < max a c := lt_of_lt_of_le hc (le_max_right _ _)
      have := Real.cosh_pos (max a c)
      positivity
  have hG2 : Continuous (fun a : ℝ => positiveShellDensity ε a * a) := by
    unfold positiveShellDensity
    exact (continuous_const.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')).mul continuous_id
  have e : saddleSourceShellDerivative ε = fun u =>
      (∫ t in c..E, (shortShellDensity ε (max t c) * max t c) * Real.sinh (u * t)) +
      (∫ t in shellLocation ε..shellLocation ε + 1, (positiveShellDensity ε t * t) * Real.sinh (u * t)) := by
    funext u
    unfold saddleSourceShellDerivative
    congr 1
    apply intervalIntegral.integral_congr
    intro a ha
    rw [Set.uIcc_of_le horder] at ha
    simp only [max_eq_left ha.1]
  rw [e]
  exact (h47_param_sinh_C1 hG1 c E).add (h47_param_sinh_C1 hG2 _ _)

