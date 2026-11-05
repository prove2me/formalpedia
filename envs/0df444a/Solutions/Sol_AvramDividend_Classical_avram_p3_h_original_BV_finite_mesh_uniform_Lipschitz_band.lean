-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:17:28.225198+00:00
-- url     : https://prove2.me/submissions/45b190ba-fafd-4a2c-9e15-c09fc0f878f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_localise_finite_interior_mesh_reserves_common_band
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original BV finite interior reserve mesh has uniform compact
Lipschitz and below-cap value envelopes for the actual stopped jump Taylor
compensation, for either finite or infinite cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (S : Finset ℝ) (hS : S.Nonempty)
    (hInside : ∀ z ∈ S, 0 < z ∧ ENNReal.ofReal z < C) :
    ∃ a b L R : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧
      (∀ z ∈ S, z ∈ Icc a b) ∧
      0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by
  obtain ⟨a, b, ha, ha2, hab, hState, hBand⟩ :=
    avram_p3_h_localise_finite_interior_mesh_reserves_common_band
      C S hS hInside
  obtain ⟨L, R, hL, hR, hLip, hWbound⟩ :=
    avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
      X hBV C w hwCont hwNeg hwC1 a b ha hab
      (avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen C) hBand
  exact ⟨a, b, L, R, ha, ha2, hab, hState, hL, hR, hLip, hWbound⟩
