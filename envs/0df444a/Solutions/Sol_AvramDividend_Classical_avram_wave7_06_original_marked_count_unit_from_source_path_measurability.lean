-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_marked_count_unit_from_source_path_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:12:30.273359+00:00
-- url     : https://prove2.me/submissions/4b95b0ca-fe70-4dd3-971f-cd16b4a7125e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original X marked count is integer-valued under fixed-path measurability. -/
theorem solution
        {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ)
    (hMark : ∀ ω : Ω, Measurable
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (hJump : ∀ ω : Ω, MeasurableSet {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0})
    (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0 →
    1 ≤ ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) := by
  classical
  intro hNonzero
  let J : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}
  let f : ℝ≥0 → ℝ≥0 × ℝ := fun u =>
    (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let B : Set (ℝ≥0 × ℝ) :=
    Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))
  have hf : Measurable f := hMark ω
  have hJ : MeasurableSet J := hJump ω
  have hB : MeasurableSet B := by
    dsimp [B]
    measurability
  have hS : MeasurableSet (f ⁻¹' B ∩ J) := (hf hB).inter hJ
  have hCount :
      ((Measure.count.restrict J).map f) B =
        (f ⁻¹' B ∩ J).encard.toENNReal := by
    rw [Measure.map_apply hf hB,
      Measure.restrict_apply (hf hB), Measure.count_apply hS]
  have hNonzeroE : (f ⁻¹' B ∩ J).encard ≠ 0 := by
    intro h0
    apply hNonzero
    change ((Measure.count.restrict J).map f) B = 0
    rw [hCount, h0]
    exact ENat.toENNReal_zero
  have hOneE : (1 : ENat) ≤ (f ⁻¹' B ∩ J).encard :=
    (ENat.one_le_iff_ne_zero).mpr hNonzeroE
  have hOneR := ENat.toENNReal_mono hOneE
  change (1 : ENNReal) ≤ ((Measure.count.restrict J).map f) B
  rw [hCount]
  simpa only [ENat.toENNReal_one] using hOneR
