-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_tail_vanishes_with_finite_weighted_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:04:24.005463+00:00
-- url     : https://prove2.me/submissions/e73cd786-3368-49b1-a870-3780c80164ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite original quadratic-weighted Levy measure has vanishing shrinking small-mark tails. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hAnti : Antitone B)
    (hInter : (⋂ n, B n) ⊆ ({0} : Set ℝ))
    (hFinite :
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2))) Set.univ < ⊤) :
    Tendsto (fun n =>
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
        (B n)) atTop (𝓝 0) := by
  let μ : Measure ℝ :=
    X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2))
  have hνzero : X.ν ({0} : Set ℝ) = 0 := by
    have hle : X.ν ({0} : Set ℝ) ≤ X.ν (Ici (0 : ℝ)) :=
      measure_mono (by simp)
    rw [X.ν_Ici] at hle
    exact le_zero_iff.mp hle
  have hμzero : μ ({0} : Set ℝ) = 0 := by
    dsimp [μ]
    rw [MeasureTheory.withDensity_apply _
      (measurableSet_singleton (0 : ℝ))]
    rw [(Measure.restrict_eq_zero).2 hνzero]
    simp
  have hInterZero : μ (⋂ n, B n) = 0 := by
    have hle : μ (⋂ n, B n) ≤ μ ({0} : Set ℝ) :=
      measure_mono hInter
    rw [hμzero] at hle
    exact le_zero_iff.mp hle
  have hFiniteB : μ (B 0) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono (subset_univ (B 0))) hFinite
  have ht : Tendsto (fun n => μ (B n)) atTop
      (𝓝 (μ (⋂ n, B n))) :=
    MeasureTheory.tendsto_measure_iInter_atTop
      (fun n => (hB n).nullMeasurableSet) hAnti ⟨0, hFiniteB⟩
  rw [hInterZero] at ht
  exact ht

