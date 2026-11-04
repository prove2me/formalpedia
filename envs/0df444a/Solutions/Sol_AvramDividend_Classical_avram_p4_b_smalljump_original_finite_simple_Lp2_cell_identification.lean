-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_simple_Lp2_cell_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:16:47.50034+00:00
-- url     : https://prove2.me/submissions/c1e7c7f2-9fb0-4159-ab55-e093207cf2d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite source predictable simple-integrand identification is linear in
its original L2 cells. Each genuine source jump-minus-compensator cell
representation is explicitly required as hCell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ {ι : Type*}
        (S : Finset ι)
        (φ : ι → Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))
        (J C : ι → Lp ℝ (2 : ℝ≥0∞) P)
        (I : Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hCell : ∀ i ∈ S, I (φ i) = J i - C i)
        (a : ι → ℝ),
        I (∑ i ∈ S, a i • φ i) = ∑ i ∈ S, a i • (J i - C i)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro ι S φ J C I hCell a
  calc
    I (∑ i ∈ S, a i • φ i) = ∑ i ∈ S, I (a i • φ i) := by
      rw [map_sum]
    _ = ∑ i ∈ S, a i • (J i - C i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, hCell i hi]
