-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_negative_Borel_finite_grid_collision_union_bound_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:51:38.821208+00:00
-- url     : https://prove2.me/submissions/8b15bb72-d4a5-4c97-bcee-58e9f82d73b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_shifted_negative_Borel_twojump_collision_bound_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (δ : ℝ≥0) (n : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let E : ℕ → Set Ω := fun i =>
      {ω | (2 : ℝ) ≤
        (NX ω (Ioc ((i : ℝ≥0) * δ)
          ((i : ℝ≥0) * δ + δ) ×ˢ B)).toReal}
    (P (⋃ i ∈ Finset.range n, E i)).toReal ≤
      (n : ℝ) * (((δ : ℝ≥0∞) * X.ν B).toReal ^ 2 / 2) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let E : ℕ → Set Ω := fun i =>
    {ω | (2 : ℝ) ≤
      (NX ω (Ioc ((i : ℝ≥0) * δ)
        ((i : ℝ≥0) * δ + δ) ×ˢ B)).toReal}
  let r : ℝ := ((δ : ℝ≥0∞) * X.ν B).toReal
  change (P (⋃ i ∈ Finset.range n, E i)).toReal ≤
    (n : ℝ) * (r ^ 2 / 2)
  have hCell (i : ℕ) : (P (E i)).toReal ≤ r ^ 2 / 2 := by
    simpa only [E, NX, r] using
      (avram_a25_original_shifted_negative_Borel_twojump_collision_bound_20261115
        X hFinite ((i : ℝ≥0) * δ) δ B hB hNeg)
  have hCellENN (i : ℕ) :
      P (E i) ≤ ENNReal.ofReal (r ^ 2 / 2) := by
    have hFin : P (E i) ≠ ⊤ := measure_ne_top P (E i)
    rw [← ENNReal.ofReal_toReal hFin]
    exact ENNReal.ofReal_le_ofReal (hCell i)
  have hUnion : P (⋃ i ∈ Finset.range n, E i) ≤
      ∑ i ∈ Finset.range n, P (E i) := by
    exact measure_biUnion_finset_le (Finset.range n) E
  have hSum : (∑ i ∈ Finset.range n, P (E i)) ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (r ^ 2 / 2) := by
    calc
      (∑ i ∈ Finset.range n, P (E i)) ≤
          ∑ i ∈ Finset.range n, ENNReal.ofReal (r ^ 2 / 2) := by
        exact Finset.sum_le_sum (fun i hi => hCellENN i)
      _ = (n : ℝ≥0∞) * ENNReal.ofReal (r ^ 2 / 2) := by
        simp [nsmul_eq_mul]
  have hFinR : (n : ℝ≥0∞) * ENNReal.ofReal (r ^ 2 / 2) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (by simp)
  calc
    (P (⋃ i ∈ Finset.range n, E i)).toReal ≤
        ((n : ℝ≥0∞) * ENNReal.ofReal (r ^ 2 / 2)).toReal :=
      ENNReal.toReal_mono hFinR (hUnion.trans hSum)
    _ = (n : ℝ) * (r ^ 2 / 2) := by
      have hq : 0 ≤ r ^ 2 / 2 := by positivity
      simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq]

