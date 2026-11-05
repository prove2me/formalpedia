-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_h_original_BV_finite_mesh_pairwise_value_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:25:24.87452+00:00
-- url     : https://prove2.me/submissions/afbf33fe-c6b4-4956-ae80-3124e065b160

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All values in one finite source reserve mesh obey one quantitative
Lipschitz estimate, ready for finite C1 Taylor/Stieltjes mesh bounds. -/
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
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ u ∈ S, ∀ v ∈ S, |w u - w v| ≤ L * |u - v| := by
  obtain ⟨a, b, L, R, ha, ha2, hab, hCover, hL, hR, hLip, hBound⟩ :=
    avram_p3_h_original_BV_finite_mesh_uniform_Lipschitz_band
      X hBV C w hwCont hwNeg hwC1 S hS hInside
  have haHalf : a / 2 ≤ a := by linarith
  refine ⟨L, hL, ?_⟩
  intro u hu v hv
  have huBand : u ∈ Icc (a / 2) b :=
    ⟨le_trans haHalf (hCover u hu).1, (hCover u hu).2⟩
  have hvBand : v ∈ Icc (a / 2) b :=
    ⟨le_trans haHalf (hCover v hv).1, (hCover v hv).2⟩
  exact hLip u huBand v hvBand
