-- Prove2me | solution 1 for AvramDividend.Classical.causal_damped_antitone_envelope_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:53:35.417882+00:00
-- url     : https://prove2.me/submissions/3fcdc42a-0033-442f-a2fc-35785e880377

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_positive_envelope_geometric_powers
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_antitone_Ioc_powers_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The Gaussian positive envelope has integrable powers with explicit decay. -/
theorem solution
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t)
    (hKanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hKcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ∃ (w : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < w ∧
      κ = (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t)) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      0 ≤ (∫ t in Ioi (0 : ℝ), κ t ∂volume) ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) < 1 ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
        (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤
          (∫ s in Ioi (0 : ℝ), κ s ∂volume) ^ (n + 1)) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 *
          (∫ s in Ioi (0 : ℝ), κ s ∂volume) ^ (n + 1)) / x) := by
  obtain ⟨w, κ, hw, hκdef, hκL1, hmass, F, hF0, hstep,
    hFL1, hFnonneg, hFmass⟩ :=
    causal_positive_envelope_geometric_powers K a β ha hK hKpos
  let ρ : ℝ := ∫ t in Ioi (0 : ℝ), κ t ∂volume
  have hκnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t := by
    intro t ht
    rw [hκdef]
    exact mul_nonneg
      (mul_nonneg (le_of_lt (inv_pos.mpr ha)) (le_of_lt (Real.exp_pos _)))
      (add_nonneg (abs_nonneg _) (hKpos t ht))
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact hκnonneg t ht.le
  have hκanti : AntitoneOn κ (Ioi (0 : ℝ)) := by
    have ht : AntitoneOn
        (fun t : ℝ => Real.exp (-w * t) * (|β| + K t))
        (Ioi (0 : ℝ)) :=
      causal_weighted_antitone_kernel K β w hw.le hKanti
        (by intro t ht; exact hKpos t ht.le)
    intro x hx y hy hxy
    rw [hκdef]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (ht hx hy hxy) (le_of_lt (inv_pos.mpr ha)))
  have hκcont : ContinuousOn κ (Ioi (0 : ℝ)) := by
    have hc :=
      causal_weighted_kernel_continuous_positive K w |β| hKcont
    have hmul : ContinuousOn
        (fun t : ℝ => a⁻¹ *
          (Real.exp (-w * t) * (|β| + K t))) (Ioi (0 : ℝ)) :=
      continuousOn_const.mul hc
    rw [hκdef]
    simpa only [mul_assoc] using hmul
  have hκmass : ∀ y : ℝ, 0 ≤ y →
      (∫ t in Ioc (0 : ℝ) y, κ t ∂volume) ≤ ρ := by
    intro y hy
    have hm := hFmass 0 y hy
    simpa [ρ, hF0] using hm
  have hquad := causal_antitone_Ioc_powers_quadratic
    κ F ρ hρ hκanti hκcont hκnonneg hκL1 hκmass
    hF0 hstep hFnonneg hFL1
    (by intro n y hy; exact hFmass n y hy)
  exact ⟨w, κ, F, hw, hκdef, hκL1, hρ, hmass,
    hF0, hstep, hFL1, hFnonneg, hFmass, hquad⟩
