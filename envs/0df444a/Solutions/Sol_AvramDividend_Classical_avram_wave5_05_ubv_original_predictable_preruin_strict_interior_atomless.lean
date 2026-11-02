-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:29:21.690455+00:00
-- url     : https://prove2.me/submissions/dde284b3-8c62-4940-ba81-1a95462029f4

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
For atomless stochastic physical-time clocks, the genuine pre-event original
source reserve shares the strict generator interior of its actual book reserve,
including when the controlled path starts exactly at a positive cap.
-/

/-- Same-X,D chronological predictable reserve is strictly in (0,C) a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        0 < Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
        ENNReal.ofReal (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C := by
  have hInside :=
    avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
      X hBV x C hC0 D hD hxc μ
  have hChron :=
    avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
      X x D hD.1.1 μ
  filter_upwards [hInside, hChron] with ω hωInside hωChron
  filter_upwards [hωInside, hωChron] with t htInside htChron
  intro hPre
  have hState := htInside hPre
  have hEq := htChron hPre.1
  constructor
  · rw [hEq]
    exact hState.1
  · rw [hEq]
    exact hState.2
