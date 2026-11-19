-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_finitecap_boundary_scalar_errors_both_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:57:55.523481+00:00
-- url     : https://prove2.me/submissions/9bcc7c2b-19b7-47b3-8488-41bd2e52a1f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_rational_corner_correction_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_admissible_upperstrip_expected_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    (∀ j : ℕ, 0 ≤ (w C.toReal -
      w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
      (C.toReal - C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) ∧
    Tendsto (fun j : ℕ =>
      (w C.toReal -
        w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
      (C.toReal - C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun j : ℕ => ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
      if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
        riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  constructor
  · intro j
    exact (avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
      C hC hFinite w hw_cont hw_smooth hw_grad j).2.2
  constructor
  · exact avram_f6_original_finitecap_rational_corner_correction_tendsto_zero
      w C hC hFinite hw_cont
  · exact avram_f6_original_finitecap_admissible_upperstrip_expected_zero
      X hBV x C hC hFinite hxc D hD n hn
