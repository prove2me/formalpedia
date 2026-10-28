-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_C1_volterra_resolvent_from_antitone_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:01:46.384133+00:00
-- url     : https://prove2.me/submissions/ea199e1e-da87-49db-9889-275275e7fcee

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_damped_antitone_envelope_quadratic
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_signed_damped_kernel_data
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_with_power_domination
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_envelope_volterra_resolvent
import Mathlib.Analysis.Calculus.ContDiff.Defs
open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The antitone Gaussian envelope gives a C1 solution of the derivative Volterra equation. -/
theorem solution
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t)
    (hKanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hKcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * g x + (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) := by
  obtain ⟨w, κ, F, hw, hκeq, hκL1, hρ0, hρ1,
      hF0, hFrec, hFL1, hFnonneg, hFmass, hFpoint⟩ :=
    causal_damped_antitone_envelope_quadratic
      K a β ha hK hKpos hKanti hKcont
  let ρ : ℝ := ∫ t in Ioi (0 : ℝ), κ t ∂volume
  have hκanti : AntitoneOn κ (Ioi (0 : ℝ)) := by
    have hbase := causal_weighted_antitone_kernel
      K β w hw.le hKanti (fun t ht => hKpos t ht.le)
    rw [hκeq]
    intro s hs t ht hst
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hbase hs ht hst) (inv_nonneg.mpr ha.le)
  have hκcont : ContinuousOn κ (Ioi (0 : ℝ)) := by
    rw [hκeq]
    have hc := causal_weighted_kernel_continuous_positive K w |β| hKcont
    have hconst : ContinuousOn (fun _ : ℝ => a⁻¹) (Ioi (0 : ℝ)) :=
      continuousOn_const
    have hproduct : ContinuousOn
        (fun t : ℝ => a⁻¹ * (Real.exp (-w * t) * (|β| + K t)))
        (Ioi (0 : ℝ)) := hconst.mul hc
    simpa only [mul_assoc] using hproduct
  have hκpos : ∀ t : ℝ, 0 < t → 0 ≤ κ t := by
    intro t ht
    rw [hκeq]
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr ha.le) (Real.exp_nonneg _))
      (add_nonneg (abs_nonneg _) (hKpos t ht.le))
  obtain ⟨k, hkdef, hkL1, hkmeas, hkcont, hkzero, hkdom0⟩ :=
    causal_gaussian_signed_damped_kernel_data
      K a β w ha hKcont hKpos (by simpa only [hκeq] using hκL1)
  have hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t := by
    simpa only [hκeq] using hkdom0
  obtain ⟨P, g, hP0, hPrec, hPL1, hPdom, hg, hgc, hgC1⟩ :=
    causal_neumann_C1_with_power_domination
      k κ F a ρ w ha hρ0 hρ1 hw.le
      hkL1 hkmeas hkcont hkzero hκL1 hκanti hκcont hκpos
      hkdom hF0 hFrec hFL1 hFnonneg hFmass hFpoint
  have hge := causal_gaussian_envelope_volterra_resolvent
    K k P F g a β w ρ ha hw.le hρ0 hρ1 hK
    hkdef hkL1 hPL1 hPrec hP0 hFL1 hPdom hFmass hg
  exact ⟨g, hgc, hgC1, fun x _ => hge x⟩