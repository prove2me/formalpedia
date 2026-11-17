-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_Borel_physical_count_grid_occupancy_coupling_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:00:22.674636+00:00
-- url     : https://prove2.me/submissions/63b42378-b70f-4912-b58f-339bdc44f8aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_count_occupied_grid_disagreement_forces_collision_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_negative_Borel_finite_grid_collision_union_bound_20261116
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
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
    let Z : ℕ → Ω → ℕ := fun n ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
    ∀ n : ℕ, 0 < n →
      (P {ω : Ω | K ω ≠ Z n ω}).toReal ≤
        (n : ℝ) * (((δ n : ℝ≥0∞) * X.ν B).toReal ^ 2 / 2) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  dsimp only
  intro n hn
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let δ : ℕ → ℝ≥0 := fun m => T / (m : ℝ≥0)
  let Z : ℕ → Ω → ℕ := fun m ω =>
    ((Finset.range m).filter (fun i : ℕ =>
      NX ω (Ioc ((i : ℝ≥0) * δ m)
        (((i + 1 : ℕ) : ℝ≥0) * δ m) ×ˢ B) ≠ 0)).card
  have hRight (i : ℕ) :
      (((i + 1 : ℕ) : ℝ≥0) * δ n) =
        (i : ℝ≥0) * δ n + δ n := by
    simp [Nat.cast_add, add_mul]
  have hPath :=
    avram_a26_original_physical_count_occupied_grid_disagreement_forces_collision_20261116
      X hFinite T B hB hNeg K hK hCount
  dsimp only at hPath
  have hAE : ∀ᵐ ω ∂P,
      ω ∈ {ω : Ω | K ω ≠ Z n ω} →
      ω ∈ (⋃ i ∈ Finset.range n,
        {ω : Ω | (2 : ℝ) ≤
          (NX ω (Ioc ((i : ℝ≥0) * δ n)
            (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B)).toReal}) := by
    filter_upwards [hPath] with ω hω
    intro hBad
    rcases hω n hn hBad with ⟨i, hi, htwo⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, htwo⟩⟩
  have hBound :=
    avram_a26_original_negative_Borel_finite_grid_collision_union_bound_20261116
      X hFinite (δ n) n B hB hNeg
  dsimp only at hBound
  have hBound' :
      (P (⋃ i ∈ Finset.range n,
        {ω : Ω | (2 : ℝ) ≤
          (NX ω (Ioc ((i : ℝ≥0) * δ n)
            (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B)).toReal})).toReal ≤
        (n : ℝ) * (((δ n : ℝ≥0∞) * X.ν B).toReal ^ 2 / 2) := by
    simpa only [NX, δ, hRight] using hBound
  change (P {ω : Ω | K ω ≠ Z n ω}).toReal ≤
      (n : ℝ) * (((δ n : ℝ≥0∞) * X.ν B).toReal ^ 2 / 2)
  have hmon := measure_mono_ae hAE
  have hfinite : P (⋃ i ∈ Finset.range n,
      {ω : Ω | (2 : ℝ) ≤
        (NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B)).toReal}) ≠ ⊤ :=
    measure_ne_top P _
  exact (ENNReal.toReal_mono hfinite hmon).trans hBound'
