-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_negative_band_exhaustion_from_cutoffs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:06:04.645417+00:00
-- url     : https://prove2.me/submissions/4596efed-3322-4433-b672-6fe67b0855cc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Every negative Borel set is exhausted by separated bands along any positive decreasing cutoffs. -/
theorem solution
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n)
    (hεAnti : Antitone ε)
    (hεzero : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    (∀ n, MeasurableSet (B ∩ Iic (-(ε n)))) ∧
    Monotone (fun n => B ∩ Iic (-(ε n))) ∧
    (⋃ n, B ∩ Iic (-(ε n))) = B ∧
    (∀ n, ∃ δ : ℝ, 0 < δ ∧ B ∩ Iic (-(ε n)) ⊆ Iic (-δ)) := by
  have hazero : Tendsto (fun n => -(ε n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using hεzero.neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact hB.inter measurableSet_Iic
  · intro i j hij y hy
    exact ⟨hy.1, le_trans hy.2 (neg_le_neg (hεAnti hij))⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      exact hn.1
    · intro hy
      have hyNeg : y < (0 : ℝ) := hBneg hy
      have hN : Ioi y ∈ 𝓝 (0 : ℝ) := isOpen_Ioi.mem_nhds hyNeg
      obtain ⟨n, hn⟩ := (hazero.eventually hN).exists
      exact Set.mem_iUnion.mpr ⟨n, ⟨hy, le_of_lt hn⟩⟩
  · intro n
    exact ⟨ε n, hεpos n, fun y hy => hy.2⟩
