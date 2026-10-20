-- Prove2me | solution 2 for CohnElkies.saddleSourceTailIntegrand_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:16:20.647199+00:00
-- url     : https://prove2.me/submissions/f1065ab8-afa9-4e82-8561-52e4d0f053ec

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
theorem h48_pw {ε ℓ u a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (ha : 0 < a)
    (hulower : -1 ≤ u)
    (huupper : u ≤ 1 + ε / 2)
    (hmargin : 0 ≤ shortMargin ε a) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (u * a) ≤
      (1 - 4 * ε) *
        upperGammaMeasureDensity ℓ (1 + u) a := by
  unfold shortShellDensity upperGammaMeasureDensity shortMargin
  unfold shortMargin at hmargin
  set m : ℝ := 1 - 10 * ε * (1 + a) with hm
  have hm1 : m ≤ 1 - 10 * ε := by nlinarith
  have hea := Real.exp_pos a
  have hEε : 1 ≤ Real.exp (ε * a) := Real.one_le_exp (by positivity)
  -- (1 - ε a) e^{ε a} ≤ 1
  have hx : (1 - ε * a) * Real.exp (ε * a) ≤ 1 := by
    have h := Real.add_one_le_exp (-(ε * a))
    have : Real.exp (-(ε * a)) * Real.exp (ε * a) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (ε * a)]
  have hmE : m * Real.exp (ε * a) ≤ 1 - 10 * ε := by
    have : m * Real.exp (ε * a) = (1 - 10 * ε * a) * Real.exp (ε * a) - 10 * ε * Real.exp (ε * a) := by
      rw [hm]; ring
    rw [this]
    have h2 : (1 - 10 * ε * a) * Real.exp (ε * a) ≤ (1 - ε * a) * Real.exp (ε * a) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; nlinarith
    nlinarith
  have hup : Real.exp ((2 * u - 1) * a) ≤ Real.exp a * Real.exp (ε * a) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have hinner : m * (Real.exp ((2 * u - 1) * a) + Real.exp (-a)) ≤
      (1 - 4 * ε) * (Real.exp a + Real.exp (-a)) := by
    have hEna := Real.exp_pos (-a)
    have h3 : m * Real.exp ((2 * u - 1) * a) ≤ m * (Real.exp a * Real.exp (ε * a)) :=
      mul_le_mul_of_nonneg_left hup hmargin
    have h4 : m * (Real.exp a * Real.exp (ε * a)) ≤ (1 - 10 * ε) * Real.exp a := by
      have := mul_le_mul_of_nonneg_left hmE hea.le
      linarith [this]
    nlinarith
  have k1 : Real.exp (-2 * a) * Real.exp (u * a) =
      Real.exp (-(1 + u) * a) * Real.exp ((2 * u - 1) * a) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have k2 : Real.exp (-2 * a) * Real.exp (-(u * a)) =
      Real.exp (-(1 + u) * a) * Real.exp (-a) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have key : m * Real.exp (-2 * a) * Real.cosh (u * a) ≤
      (1 - 4 * ε) * Real.exp (-(1 + u) * a) * Real.cosh a := by
    rw [Real.cosh_eq, Real.cosh_eq]
    have e : m * Real.exp (-2 * a) * ((Real.exp (u * a) + Real.exp (-(u * a))) / 2) =
        Real.exp (-(1 + u) * a) * (m * (Real.exp ((2 * u - 1) * a) + Real.exp (-a))) / 2 := by
      rw [show m * Real.exp (-2 * a) * ((Real.exp (u * a) + Real.exp (-(u * a))) / 2) =
        m * (Real.exp (-2 * a) * Real.exp (u * a) + Real.exp (-2 * a) * Real.exp (-(u * a))) / 2 by ring,
        k1, k2]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hinner (Real.exp_pos (-(1 + u) * a)).le
    nlinarith
  -- denominator bound
  have hden_pos : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    have : Real.exp (-(2 * a / ℓ)) < Real.exp 0 := Real.exp_lt_exp.mpr (show -(2 * a / ℓ) < 0 by
      have : 0 < 2 * a / ℓ := by positivity
      linarith)
    rw [Real.exp_zero] at this
    linarith
  have hden_le : 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ := by
    have := Real.add_one_le_exp (-(2 * a / ℓ)); linarith
  have hcosh := Real.cosh_pos a
  have h14 : 0 ≤ 1 - 4 * ε := by linarith
  -- assemble
  have lhs_eq : ℓ * -(-(m * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a))) * Real.cosh (u * a) =
      ℓ / (2 * a ^ 2) * (m * Real.exp (-2 * a) * Real.cosh (u * a) / Real.cosh a) := by
    field_simp
  rw [lhs_eq, mul_div_assoc' (1 - 4 * ε)]
  calc ℓ / (2 * a ^ 2) * (m * Real.exp (-2 * a) * Real.cosh (u * a) / Real.cosh a)
      ≤ ℓ / (2 * a ^ 2) * ((1 - 4 * ε) * Real.exp (-(1 + u) * a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hcosh]; exact key
    _ = (1 - 4 * ε) * Real.exp (-(1 + u) * a) / (a * (2 * a / ℓ)) := by
        field_simp
    _ ≤ (1 - 4 * ε) * Real.exp (-(1 + u) * a) / (a * (1 - Real.exp (-(2 * a / ℓ)))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hden_le ha.le

theorem h48_dens_nonneg (ℓ η : ℝ) {a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    0 ≤ upperGammaMeasureDensity ℓ η a := by
  unfold upperGammaMeasureDensity
  have : Real.exp (-(2 * a / ℓ)) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(2 * a / ℓ) < 0 by
      have : 0 < 2 * a / ℓ := by positivity
      linarith)
    rwa [Real.exp_zero] at h
  have : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  positivity

theorem h48_sq_dens_le (ℓ η : ℝ) {a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    a ^ 2 * upperGammaMeasureDensity ℓ η a ≤ (ℓ / 2 + a) * Real.exp (-η * a) := by
  unfold upperGammaMeasureDensity
  set x : ℝ := 2 * a / ℓ with hx
  have hxpos : 0 < x := by positivity
  have hE : Real.exp (-x) * (1 + x) ≤ 1 := by
    have h1 := Real.add_one_le_exp x
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-x)]
  have hden : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hdpos : 0 < 1 - Real.exp (-x) := lt_of_lt_of_le (by positivity) hden
  have he := Real.exp_pos (-η * a)
  rw [show a ^ 2 * (Real.exp (-η * a) / (a * (1 - Real.exp (-x)))) =
    a * Real.exp (-η * a) / (1 - Real.exp (-x)) by field_simp]
  rw [div_le_iff₀ hdpos]
  have : (ℓ / 2 + a) * (x / (1 + x)) = a := by
    rw [hx]; field_simp
  calc a * Real.exp (-η * a) = Real.exp (-η * a) * ((ℓ / 2 + a) * (x / (1 + x))) := by rw [this]; ring
    _ ≤ Real.exp (-η * a) * ((ℓ / 2 + a) * (1 - Real.exp (-x))) := by
        gcongr
    _ = _ := by ring

theorem h48_dens_contOn (ℓ η : ℝ) (hℓ : 0 < ℓ) :
    ContinuousOn (upperGammaMeasureDensity ℓ η) (Set.Ioi 0) := by
  unfold upperGammaMeasureDensity
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro a ha
  have ha' : (0:ℝ) < a := ha
  have : Real.exp (-(2 * a / ℓ)) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(2 * a / ℓ) < 0 by
      have : 0 < 2 * a / ℓ := by positivity
      linarith)
    rwa [Real.exp_zero] at h
  have : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  positivity

theorem h48_majorant_int (ℓ η : ℝ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ => (ℓ / 2 + a) * Real.exp (-η * a)) (Set.Ioi 0) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (0 : ℝ)) (p := 1) (b := η)
    (by norm_num) one_pos hη
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := 1) (b := η)
    (by norm_num) one_pos hη
  have := (h0.const_mul (ℓ / 2)).add h1
  refine IntegrableOn.congr_fun this (fun a ha => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Real.rpow_zero, Real.rpow_one]
  ring

theorem h48_int_var (ℓ η : ℝ) (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ => a ^ 2 * upperGammaMeasureDensity ℓ η a) (Set.Ioi 0) := by
  refine (h48_majorant_int ℓ η hη).mono' ?_ ?_
  · exact ((continuousOn_id.pow 2).mul (h48_dens_contOn ℓ η hℓ)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun a ha => ?_))
    have ha' : (0:ℝ) < a := ha
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (h48_dens_nonneg ℓ η hℓ ha'))]
    exact h48_sq_dens_le ℓ η hℓ ha'

theorem h48_int_damp (ℓ η T : ℝ) (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ => upperGammaDampingIntegrand ℓ η T a) (Set.Ioi 0) := by
  refine ((h48_int_var ℓ η hℓ hη).const_mul (T ^ 2 / 2)).mono' ?_ ?_
  · unfold upperGammaDampingIntegrand
    exact ((Continuous.continuousOn (by fun_prop)).mul (h48_dens_contOn ℓ η hℓ)).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun a ha => ?_))
    have ha' : (0:ℝ) < a := ha
    unfold upperGammaDampingIntegrand
    have hd := h48_dens_nonneg ℓ η hℓ ha'
    have hc : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
    have hc2 : 1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := a * T); linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hd)]
    calc (1 - Real.cos (a * T)) * upperGammaMeasureDensity ℓ η a
        ≤ (a * T) ^ 2 / 2 * upperGammaMeasureDensity ℓ η a := mul_le_mul_of_nonneg_right hc2 hd
      _ = T ^ 2 / 2 * (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by ring

theorem h48_cont_shell (ρ : ℝ → ℝ) (x y : ℝ) (hρ : IntervalIntegrable ρ volume x y) (c : ℝ) :
    Continuous (fun T : ℝ => ∫ a in x..y, ρ a * Real.cosh (c * a) * (1 - Real.cos (a * T))) := by
  have hρm : AEStronglyMeasurable ρ (volume.restrict (Set.uIoc x y)) := hρ.def'.aestronglyMeasurable
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun a => ‖ρ a‖ * ‖Real.cosh (c * a)‖ * 2)
  · intro T
    exact (hρm.mul (Continuous.aestronglyMeasurable (f := fun a : ℝ => Real.cosh (c * a)) (by fun_prop))).mul
      (Continuous.aestronglyMeasurable (f := fun a : ℝ => 1 - Real.cos (a * T)) (by fun_prop))
  · intro T
    refine Filter.Eventually.of_forall (fun a _ => ?_)
    rw [norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.cos_le_one (a * T), Real.neg_one_le_cos (a * T)]
  · exact (hρ.norm.mul_continuousOn (Continuous.continuousOn
      (f := fun a : ℝ => ‖Real.cosh (c * a)‖) (by fun_prop))).mul_const 2
  · exact Filter.Eventually.of_forall (fun a _ => by fun_prop)

theorem h48_cont_gamma (ℓ η : ℝ) (hℓ : 0 < ℓ) (hη : 0 < η) :
    Continuous (fun T : ℝ => upperGammaDamping ℓ η T) := by
  rw [continuous_iff_continuousAt]
  intro T0
  unfold upperGammaDamping
  apply MeasureTheory.continuousAt_of_dominated
    (bound := fun a => ((|T0| + 1) ^ 2 / 2) * (a ^ 2 * upperGammaMeasureDensity ℓ η a))
  · refine Filter.Eventually.of_forall (fun T => ?_)
    unfold upperGammaDampingIntegrand
    exact ((Continuous.continuousOn (f := fun a : ℝ => 1 - Real.cos (a * T)) (by fun_prop)).mul
      (h48_dens_contOn ℓ η hℓ)).aestronglyMeasurable measurableSet_Ioi
  · have hball : Metric.ball T0 1 ∈ nhds T0 := Metric.ball_mem_nhds T0 one_pos
    filter_upwards [hball] with T hT
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun a ha => ?_))
    have ha' : (0:ℝ) < a := ha
    have hTb : |T| ≤ |T0| + 1 := by
      have : |T - T0| < 1 := by simpa [Real.dist_eq] using hT
      have := abs_sub_abs_le_abs_sub T T0
      linarith
    unfold upperGammaDampingIntegrand
    have hd := h48_dens_nonneg ℓ η hℓ ha'
    have hc : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
    have hc2 : 1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := a * T); linarith
    have hT2 : T ^ 2 ≤ (|T0| + 1) ^ 2 := by
      rw [← sq_abs T]; exact pow_le_pow_left₀ (abs_nonneg _) hTb 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hd)]
    calc (1 - Real.cos (a * T)) * upperGammaMeasureDensity ℓ η a
        ≤ (a * T) ^ 2 / 2 * upperGammaMeasureDensity ℓ η a := mul_le_mul_of_nonneg_right hc2 hd
      _ = T ^ 2 / 2 * (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by ring
      _ ≤ (|T0| + 1) ^ 2 / 2 * (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (sq_nonneg _) hd); linarith
  · exact ((h48_int_var ℓ η hℓ hη).const_mul _)
  · exact Filter.Eventually.of_forall (fun a => by unfold upperGammaDampingIntegrand; fun_prop)

theorem solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  have hη : 0 < 1 + u := by linarith
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hp : IntervalIntegrable (positiveShellDensity ε) volume
      (shellLocation ε) (shellLocation ε + 1) :=
    (positiveShellDensity_continuous ε).intervalIntegrable _ _
  have hG := h48_cont_gamma ℓ (1 + u) hℓ hη
  have hP := (h48_cont_shell _ _ _ hp (1 + (u - 1))).const_mul ℓ
  have hS := (h48_cont_shell _ _ _ hs.neg (1 + (u - 1))).const_mul ℓ
  have hD : Continuous (fun T : ℝ => saddleSourceContourDamping ε ℓ u T) := by
    unfold saddleSourceContourDamping positiveShellDamping upperShortShellDamping
    exact (hG.add hP).sub hS
  unfold saddleGaussianTailWeight
  exact (continuous_const.add (continuous_abs.pow 3)).mul (Real.continuous_exp.comp hD.neg)

