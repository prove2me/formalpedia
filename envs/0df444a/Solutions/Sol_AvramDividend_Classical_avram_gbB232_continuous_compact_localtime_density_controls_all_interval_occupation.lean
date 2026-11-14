-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB232_continuous_compact_localtime_density_controls_all_interval_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:24.601356+00:00
-- url     : https://prove2.me/submissions/90b03be0-8d4e-4061-b11f-ec471d77890e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB231_continuous_compact_support_occupation_density_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB176_bounded_occupation_density_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- A continuous compact local-time density bounds every spatial occupation interval. -/
theorem solution
    (f : ℝ → ℝ) (n : ℕ) (ρ : ℝ)
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hContinuous : Continuous ℓ)
    (hNonneg : ∀ z, 0 ≤ ℓ z)
    (hSupport : ∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0)
    (hOccupation : ∀ a b : ℝ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t ∈ Set.Ioo a b} =
      ∫⁻ z in Set.Ioo a b, ENNReal.ofReal (ℓ z) ∂volume) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℝ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t ∈ Set.Ioo a b} ≤
      ENNReal.ofReal B * volume (Set.Ioo a b) := by
  obtain ⟨B, hB0, hBd⟩ :=
    avram_gbB231_continuous_compact_support_occupation_density_uniform_bound
      ℓ R hContinuous hNonneg hSupport
  refine ⟨B, hB0, ?_⟩
  intro a b
  calc
    volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
      f t ∈ Set.Ioo a b} =
      ∫⁻ z in Set.Ioo a b, ENNReal.ofReal (ℓ z) ∂volume :=
        hOccupation a b
    _ ≤ ENNReal.ofReal B * volume (Set.Ioo a b) :=
      avram_gbB176_bounded_occupation_density_lintegral
        (fun z => ENNReal.ofReal (ℓ z)) (ENNReal.ofReal B)
        a b (fun z => ENNReal.ofReal_le_ofReal (hBd z))
