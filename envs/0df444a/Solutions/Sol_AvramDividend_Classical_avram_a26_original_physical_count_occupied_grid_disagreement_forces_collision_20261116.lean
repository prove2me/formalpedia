-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_physical_count_occupied_grid_disagreement_forces_collision_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:15:57.261983+00:00
-- url     : https://prove2.me/submissions/4eb5f55f-b8b9-4198-aca5-3be0f86fd130

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_finite_marked_support_grid_mismatch_forces_double_source_cell_20261116
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
    ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n →
      K ω ≠ Z n ω →
      ∃ i ∈ Finset.range n,
        (2 : ℝ) ≤
          (NX ω (Ioc ((i : ℝ≥0) * δ n)
            (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B)).toReal := by
  classical
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
  change ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n →
    K ω ≠ Z n ω →
    ∃ i ∈ Finset.range n,
      (2 : ℝ) ≤ (NX ω (Ioc ((i : ℝ≥0) * δ n)
        (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B)).toReal
  filter_upwards [
    avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
      X hFinite T B hB hNeg K hK hCount] with ω hω
  obtain ⟨S, hS, hKω⟩ := hω
  intro n hn hDiff
  have hSource :=
    avram_a27_original_finite_marked_support_grid_mismatch_forces_double_source_cell_20261116
      X ω T B hB S hS n hn
  dsimp only at hSource
  apply hSource
  simpa only [hKω, NX, δ, Z] using hDiff
