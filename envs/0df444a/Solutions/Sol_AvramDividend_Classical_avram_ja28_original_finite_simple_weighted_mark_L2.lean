-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja28_original_finite_simple_weighted_mark_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:37:12.0182+00:00
-- url     : https://prove2.me/submissions/9de4f15e-d987-4982-816f-298f0a1304db

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (k : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range k, MeasurableSet (B i))
    (hNeg : ∀ i ∈ Finset.range k, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k,
      i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let A : ℕ → Ω → ℝ := fun i ω =>
      c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    (∫ ω, (∑ i ∈ Finset.range k, A i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range k, (c i) ^ 2 * r i  := by
  classical
  simpa only using
    (avram_ja31_original_finite_borel_mark_source_isometry
      X hFinite T (Finset.range k) B c hB hNeg hDisj).2
