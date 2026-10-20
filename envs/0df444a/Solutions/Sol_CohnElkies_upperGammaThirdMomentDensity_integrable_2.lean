-- Prove2me | solution 2 for CohnElkies.upperGammaThirdMomentDensity_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:00.076344+00:00
-- url     : https://prove2.me/submissions/c0445eb6-e46b-4f95-96ba-4fb308f77209

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


theorem solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn
      (fun a : ℝ => a ^ 3 * upperGammaMeasureDensity ℓ η a)
      (Set.Ioi 0) := by
  have hI : ∀ s : ℝ, -1 < s → IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-η * x)) (Ioi 0) := by
    intro s hs
    have := integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hη
    simpa [Real.rpow_one] using this
  have hmaj : IntegrableOn (fun a : ℝ => a ^ (2:ℝ) * Real.exp (-η * a) +
      (ℓ / 2) * (a ^ (1:ℝ) * Real.exp (-η * a))) (Ioi 0) :=
    (hI 2 (by norm_num)).add ((hI 1 (by norm_num)).const_mul _)
  have hden : ∀ a : ℝ, 0 < a → 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    intro a ha
    have : Real.exp (-(2 * a / ℓ)) < 1 :=
      Real.exp_lt_one_iff.2 (by have := div_pos (by linarith : 0 < 2*a) hℓ; linarith)
    linarith
  refine hmaj.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    unfold upperGammaMeasureDensity
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    exact mul_ne_zero (ne_of_gt ha) (hden a ha).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have ha0 : 0 < a := ha
    have hd := hden a ha0
    have he := Real.exp_pos (-η * a)
    unfold upperGammaMeasureDensity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_two, Real.rpow_one]
    set y := 2 * a / ℓ with hy
    have hy0 : 0 < y := by positivity
    have hq : Real.exp (-y) * (1 + y) ≤ 1 := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos y)]
      linarith [Real.add_one_le_exp y]
    rw [show a ^ 3 * (Real.exp (-η * a) / (a * (1 - Real.exp (-y)))) =
        a ^ 2 * Real.exp (-η * a) / (1 - Real.exp (-y)) by field_simp]
    rw [div_le_iff₀ hd]
    have hyl : y * ℓ = 2 * a := by rw [hy]; field_simp
    have h1 : 0 ≤ a * Real.exp (-η * a) * ℓ / 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hq h1
    have hay : a = y * ℓ / 2 := by linarith
    have h3 : a * (a * Real.exp (-η * a)) = y * ℓ / 2 * (a * Real.exp (-η * a)) := by rw [← hay]
    have h4 : a * (a * Real.exp (-η * a)) * Real.exp (-y) =
        y * ℓ / 2 * (a * Real.exp (-η * a)) * Real.exp (-y) := by rw [← hay]
    nlinarith [h2, h3, h4]

