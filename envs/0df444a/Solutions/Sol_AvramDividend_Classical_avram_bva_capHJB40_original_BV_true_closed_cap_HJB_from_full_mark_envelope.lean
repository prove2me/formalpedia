-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB40_original_BV_true_closed_cap_HJB_from_full_mark_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:56:29.794642+00:00
-- url     : https://prove2.me/submissions/8c294499-62f9-4ce6-903a-76faf018771f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB38_original_BV_boundary_unmasked_sign_of_dominated_source
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB39_original_continuity_away_from_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℕ → ℝ)
    (hy : Tendsto y atTop (𝓝 C.toReal))
    (hyInside : ∀ n, 0 < y n ∧ ENNReal.ofReal (y n) < C)
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))))
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun z : ℝ => w (y n + z) - w (y n))
      (X.ν.restrict (Iio (0 : ℝ))))
    (hDom : ∀ n, ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖w (y n + z) - w (y n)‖ ≤ ‖g z‖) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0 := by
  have hcpos : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFinite
  have hcIci : Ici (0 : ℝ) ∈ 𝓝 C.toReal :=
    Filter.mem_of_superset (Ioi_mem_nhds hcpos) Ioi_subset_Ici_self
  have hwc : ContinuousAt w C.toReal :=
    hwCont.continuousAt hcIci
  have hAway : ∀ r : ℝ, r ≠ 0 → ContinuousAt w r := by
    intro r hr
    exact avram_bva_capHJB39_original_continuity_away_from_zero
      w hwCont hwNeg r hr
  exact avram_bva_capHJB38_original_BV_boundary_unmasked_sign_of_dominated_source
    X hStanding hBV q w C hC hFinite hwc hAway
    hwGen hwGrad y hy hyInside g hg hMeas hDom
