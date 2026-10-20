-- Prove2me | solution 2 for CohnElkies.upperGammaDampingIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:17.344648+00:00
-- url     : https://prove2.me/submissions/ef57eb4c-51a3-4bc4-bab0-1ac1b4c34353

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
theorem h47_exp_lt_one {x : ℝ} (h : x < 0) : Real.exp x < 1 := by
  simpa using Real.exp_lt_exp.mpr h

theorem solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    IntegrableOn
      (upperGammaDampingIntegrand ℓ η T) (Ioi 0) := by
  have hg : IntegrableOn (fun a : ℝ => T ^ 2 / 4 * (ℓ + 4 / η) * Real.exp (-(η / 2) * a)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(η / 2) < 0) 0).const_mul _
  have hcont : ContinuousOn (upperGammaDampingIntegrand ℓ η T) (Ioi 0) := by
    unfold upperGammaDampingIntegrand upperGammaMeasureDensity
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    have ha0 : (0:ℝ) < a := ha
    have := h47_exp_lt_one (by
      have : 0 < 2 * a / ℓ := by positivity
      linarith : -(2 * a / ℓ) < 0)
    exact (mul_pos ha0 (by linarith)).ne'
  refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun a ha => ?_))
  have ha0 : (0:ℝ) < a := ha
  have hx : 0 < 2 * a / ℓ := by positivity
  have hxe : Real.exp (-(2 * a / ℓ)) < 1 := h47_exp_lt_one (by linarith)
  have hD0 : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  have hDlow : 2 * a / (ℓ + 2 * a) ≤ 1 - Real.exp (-(2 * a / ℓ)) := by
    have h1 := Real.add_one_le_exp (2 * a / ℓ)
    have h2 : Real.exp (-(2 * a / ℓ)) * Real.exp (2 * a / ℓ) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : Real.exp (-(2 * a / ℓ)) * (2 * a / ℓ + 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(2 * a / ℓ))).le
      linarith
    have h5 : ℓ * (2 * a / ℓ) = 2 * a := by field_simp
    rw [div_le_iff₀ (by positivity)]
    have h4 : ℓ + 2 * a = ℓ * (2 * a / ℓ + 1) := by linarith
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_left h3 hℓ.le]
  have hcos : 1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := a * T)]
  have hcos0 : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
  have hE2 : Real.exp (-(η / 2) * a) ^ 2 = Real.exp (-η * a) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE1 : Real.exp (-(η / 2) * a) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hF := Real.add_one_le_exp ((η / 2) * a)
  have hEF : Real.exp (-(η / 2) * a) * Real.exp ((η / 2) * a) = 1 := by
    rw [← Real.exp_add]; simp
  have hE0 := Real.exp_pos (-(η / 2) * a)
  have haE : a * Real.exp (-(η / 2) * a) ≤ 2 / η := by
    rw [le_div_iff₀ hη]
    nlinarith [mul_le_mul_of_nonneg_left hF hE0.le]
  have hDpos : 0 < a * (1 - Real.exp (-(2 * a / ℓ))) := mul_pos ha0 hD0
  have hfnn : 0 ≤ upperGammaDampingIntegrand ℓ η T a := by
    unfold upperGammaDampingIntegrand upperGammaMeasureDensity
    exact mul_nonneg hcos0 (div_nonneg (Real.exp_pos _).le hDpos.le)
  rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  unfold upperGammaDampingIntegrand upperGammaMeasureDensity
  rw [mul_div_assoc', div_le_iff₀ hDpos, ← hE2]
  have hlow : a * (2 * a / (ℓ + 2 * a)) ≤ a * (1 - Real.exp (-(2 * a / ℓ))) :=
    mul_le_mul_of_nonneg_left hDlow ha0.le
  have hgnn : 0 ≤ T ^ 2 / 4 * (ℓ + 4 / η) * Real.exp (-(η / 2) * a) := by positivity
  have hinner : Real.exp (-(η / 2) * a) ^ 2 * (ℓ + 2 * a) ≤
      (ℓ + 4 / η) * Real.exp (-(η / 2) * a) := by
    have i1 := mul_le_mul_of_nonneg_left hE1 (mul_nonneg hℓ.le hE0.le)
    have i2 := mul_le_mul_of_nonneg_left haE hE0.le
    have e1 : Real.exp (-(η / 2) * a) ^ 2 * (ℓ + 2 * a) =
        ℓ * Real.exp (-(η / 2) * a) * Real.exp (-(η / 2) * a) +
          2 * (Real.exp (-(η / 2) * a) * (a * Real.exp (-(η / 2) * a))) := by ring
    have e2 : (ℓ + 4 / η) * Real.exp (-(η / 2) * a) =
        ℓ * Real.exp (-(η / 2) * a) * 1 + 2 * (Real.exp (-(η / 2) * a) * (2 / η)) := by ring
    rw [e1, e2]
    linarith
  generalize Real.exp (-(η / 2) * a) = E at *
  have hpos : 0 < ℓ + 2 * a := by positivity
  have hkey : (a * T) ^ 2 / 2 * E ^ 2 ≤ T ^ 2 / 4 * (ℓ + 4 / η) * E * (a * (2 * a / (ℓ + 2 * a))) := by
    have e : T ^ 2 / 4 * (ℓ + 4 / η) * E * (a * (2 * a / (ℓ + 2 * a))) =
        (a * T) ^ 2 / 2 * ((ℓ + 4 / η) * E) / (ℓ + 2 * a) := by
      field_simp
      ring
    rw [e, le_div_iff₀ hpos]
    calc (a * T) ^ 2 / 2 * E ^ 2 * (ℓ + 2 * a) = (a * T) ^ 2 / 2 * (E ^ 2 * (ℓ + 2 * a)) := by ring
      _ ≤ (a * T) ^ 2 / 2 * ((ℓ + 4 / η) * E) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
  calc (1 - Real.cos (a * T)) * E ^ 2 ≤ (a * T) ^ 2 / 2 * E ^ 2 :=
        mul_le_mul_of_nonneg_right hcos (sq_nonneg _)
    _ ≤ T ^ 2 / 4 * (ℓ + 4 / η) * E * (a * (2 * a / (ℓ + 2 * a))) := hkey
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hgnn

