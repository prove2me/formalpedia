-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_simple_borel_partition_raw_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T20:54:31.876833+00:00
-- url     : https://prove2.me/submissions/5ade87a1-a6e0-47b5-978c-12c2eb26b4e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
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
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ)) (g : SimpleFunc ℝ ℝ) :
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℝ → ℝ := fun y => ((T : ℝ≥0∞) * X.ν (B y)).toReal
    let J : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y * (NX ω (Ioc 0 T ×ˢ B y)).toReal
    let m : ℝ := ∑ y ∈ g.range, y * r y
    let v : ℝ := ∑ y ∈ g.range, y ^ 2 * r y
    Integrable J P ∧ Integrable (fun ω => J ω ^ 2) P ∧
      (∫ ω, J ω ∂P) = m ∧
      (∫ ω, J ω ^ 2 ∂P) = m ^ 2 + v := by
  classical
  intro B NX r J m v
  have hB : ∀ y ∈ g.range, MeasurableSet (B y) := by
    intro y hy
    exact hS.inter (g.measurableSet_fiber y)
  have hBNeg : ∀ y ∈ g.range, B y ⊆ Iio (0 : ℝ) := by
    intro y hy w hw
    exact hNeg hw.1
  have hDisj : ∀ y ∈ g.range, ∀ z ∈ g.range,
      y ≠ z → Disjoint (B y) (B z) := by
    intro y hy z hz hne
    apply Set.disjoint_left.mpr
    intro w hw1 hw2
    apply hne
    have h1 : g w = y := hw1.2
    have h2 : g w = z := hw2.2
    exact h1.symm.trans h2
  simpa only [B, NX, r, J, m, v] using
    (avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
      X hFinite T g.range B (fun y => y) hB hBNeg hDisj)
