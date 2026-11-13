-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja31_original_finite_borel_mark_source_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:07:27.796505+00:00
-- url     : https://prove2.me/submissions/611f02db-b5c7-4b61-9497-690923cd2e0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja29_original_finite_borel_mark_simple_isometry
import Theorems.Thm_AvramDividend_Classical_avram_ja30_original_negative_borel_partition_count_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Source-faithful finite mark isometry from physical Borel count moments. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (F : Finset ι) (B : ι → Set ℝ) (a : ι → ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hNeg : ∀ i ∈ F, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
    Integrable (fun ω => (∑ i ∈ F, a i * Y i ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ F, a i * Y i ω) ^ 2 ∂P) =
        ∑ i ∈ F, (a i) ^ 2 * r i := by
  obtain ⟨hDiag, hOff⟩ :=
    avram_ja30_original_negative_borel_partition_count_moments
      X hFinite T F B hB hNeg hDisj
  exact avram_ja29_original_finite_borel_mark_simple_isometry
    X T F B a hB hDisj hDiag hOff
