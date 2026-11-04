-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_weighted_future_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:38:29.199584+00:00
-- url     : https://prove2.me/submissions/8c114304-cb43-4672-93ba-4c05e244022d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original-process future increment path factors against any
nonnegative past-measurable weight, with no boundedness or finite-mean premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, W ω * F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) =
    (∫⁻ ω, W ω ∂P) *
      (∫⁻ ω, F (fun v : ℝ≥0 => X.X v ω) ∂P) := by
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω v => X.X (s + v) ω - X.X s ω
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω v => X.X v ω
  let μ : Measure (ℝ≥0 → ℝ) := Measure.map Z P
  let rate : ℝ≥0∞ := ∫⁻ y, F y ∂μ
  have hWm : Measurable W := hW.mono (𝓕.le s) le_rfl
  have hZm : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro v
    exact (X.adapted v).mono (𝓕.le v) le_rfl
  have hf : Measurable
      (fun p : ℝ≥0∞ × (ℝ≥0 → ℝ) => p.1 * F p.2) :=
    measurable_fst.mul (hF.comp measurable_snd)
  have hKernel :
      (∫⁻ ω, W ω * F (Y ω) ∂P) =
      (∫⁻ ω, ∫⁻ y, W ω * F y ∂μ ∂P) := by
    simpa only [Set.mem_univ, if_true] using
      (avram_root29_01_original_future_kernel_past_test
        X s W hW Set.univ MeasurableSet.univ
        (fun p : ℝ≥0∞ × (ℝ≥0 → ℝ) => p.1 * F p.2) hf)
  have hRate : rate = ∫⁻ ω, F (Z ω) ∂P := by
    exact lintegral_map hF hZm
  change (∫⁻ ω, W ω * F (Y ω) ∂P) =
    (∫⁻ ω, W ω ∂P) * (∫⁻ ω, F (Z ω) ∂P)
  calc
    (∫⁻ ω, W ω * F (Y ω) ∂P) =
        (∫⁻ ω, ∫⁻ y, W ω * F y ∂μ ∂P) := hKernel
    _ = ∫⁻ ω, W ω * rate ∂P := by
        apply lintegral_congr
        intro ω
        exact lintegral_const_mul (W ω) hF
    _ = (∫⁻ ω, W ω ∂P) * rate :=
      lintegral_mul_const rate hWm
    _ = (∫⁻ ω, W ω ∂P) * (∫⁻ ω, F (Z ω) ∂P) := by
      rw [hRate]
