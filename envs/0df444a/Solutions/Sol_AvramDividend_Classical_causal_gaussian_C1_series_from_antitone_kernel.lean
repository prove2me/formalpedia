-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_C1_series_from_antitone_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:09:45.744679+00:00
-- url     : https://prove2.me/submissions/95a8e27a-bd5b-4e4b-85bd-fa072bdc939d

import Theorems.Thm_AvramDividend_Classical_causal_damped_antitone_envelope_quadratic
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_signed_damped_kernel_data
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_from_antitone_envelope_powers

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A Gaussian antitone L1 kernel yields an explicit C1 Neumann candidate. -/
theorem solution
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t)
    (hKanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hKcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ∃ (w : ℝ) (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ) (g : ℝ → ℝ),
      0 < w ∧
      k = (fun t : ℝ =>
        if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0) ∧
      P 0 = k ∧
      (∀ n : ℕ, P (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume) ∧
      (g = fun y : ℝ => 1 / a + Real.exp (w * y) *
        (∑' n : ℕ, (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P n s ∂volume)) / a)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by
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
  obtain ⟨P, g, hP0, hPrec, hg, hgc, hgC1⟩ :=
    causal_neumann_C1_from_antitone_envelope_powers
      k κ F a ρ w ha hρ0 hρ1 hw.le
      hkL1 hkmeas hkcont hkzero hκL1 hκanti hκcont hκpos
      hkdom hF0 hFrec hFL1 hFnonneg hFmass hFpoint
  exact ⟨w, k, P, g, hw, hkdef, hP0, hPrec, hg, hgc, hgC1⟩
