-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_union_marks_twojump_collision
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:26:55.274024+00:00
-- url     : https://prove2.me/submissions/482e1766-b5e6-4fcb-b511-60be1c878e39

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_physical_twojump_collision_bound_20261115
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (δ : ℝ≥0) :
    (P {ω : Ω | (2 : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 δ ×ˢ (⋃ i, B i))).toReal}).toReal ≤
      (((δ : ℝ≥0∞) * X.ν (⋃ i, B i)).toReal) ^ 2 / 2 := by
  have hUnionMeas : MeasurableSet (⋃ i : Fin n, B i) :=
    MeasurableSet.iUnion hMeas
  have hUnionNeg : (⋃ i : Fin n, B i) ⊆ Iio (0 : ℝ) := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    exact hNeg i hi
  exact avram_a25_original_negative_Borel_physical_twojump_collision_bound_20261115
    X hFinite δ (⋃ i, B i) hUnionMeas hUnionNeg
