-- Prove2me | solution 1 for AvramDividend.Classical.causal_positive_envelope_geometric_powers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:40:43.864091+00:00
-- url     : https://prove2.me/submissions/8fb57c7a-3850-45fa-a347-b61785f6003d

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_exists_contracting_weighted_envelope
import Theorems.Thm_AvramDividend_Classical_causal_positive_convolution_powers_geometric_truncated_mass

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A Gaussian-positive causal kernel admits geometric convolution powers. -/
theorem solution
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t) :
    ∃ (w : ℝ) (κ : ℝ → ℝ),
      0 < w ∧
      κ = (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t)) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) < 1 ∧
      ∃ F : ℕ → ℝ → ℝ,
        F 0 = κ ∧
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
            κ s * F n (x - s) ∂volume) ∧
        (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
        (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
        (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
          (∫ t in Ioc (0 : ℝ) x, F n t ∂volume) ≤
          (∫ t in Ioi (0 : ℝ), κ t ∂volume) ^ (n + 1)) := by
  obtain ⟨w, hw, hI, hmass⟩ :=
    causal_l1_exists_contracting_weighted_envelope K a β ha hK
  let κ : ℝ → ℝ :=
    fun t => a⁻¹ * Real.exp (-w * t) * (|β| + K t)
  have hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t := by
    intro t ht
    have hi : 0 ≤ a⁻¹ := le_of_lt (inv_pos.mpr ha)
    have he : 0 ≤ Real.exp (-w * t) := le_of_lt (Real.exp_pos _)
    have hk : 0 ≤ |β| + K t :=
      add_nonneg (abs_nonneg β) (hKpos t ht)
    exact mul_nonneg (mul_nonneg hi he) hk
  obtain ⟨F, hzero, hstep, hIF, hFpos, hbound⟩ :=
    causal_positive_convolution_powers_geometric_truncated_mass
      κ hI hκpos
  exact ⟨w, κ, hw, rfl, hI, hmass, F, hzero, hstep,
    hIF, hFpos, hbound⟩
