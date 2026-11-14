-- Prove2me | solution 1 for AvramDividend.Classical.avram_b35_original_physical_C2_Taylor_zero_increment_cell_filter_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:23.778952+00:00
-- url     : https://prove2.me/submissions/261143a7-72d6-47b6-838e-65a3555281e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original physical C2 Taylor mesh remainder discards zero-displacement source cells. -/
theorem solution
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration ℝ≥0 mOmega}
    (X : SpectrallyNegativeLevy P F)
    (x : ℝ) (D : ℝ≥0 → Omega → ℝ)
    (w : ℝ → ℝ) (S : Finset ℕ)
    (s t : ℕ → Omega → ℝ≥0) :
    ∀ omega : Omega,
      let z : ℕ → ℝ := fun i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u omega - rightLimit D u omega) (s i omega)
      let g : ℕ → ℝ := fun i =>
        X.X (t i omega) omega - X.X (s i omega) omega -
          (((t i omega : ℝ) - (s i omega : ℝ)) * X.c)
      let R : ℕ → ℝ := fun i =>
        (w (z i + g i) -
          taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
            (z i) (z i + g i) -
          (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2)
      (∑ i ∈ S, R i) =
        (∑ i ∈ S.filter (fun i => g i ≠ 0), R i) := by
  classical
  intro omega
  dsimp only
  let z : ℕ → ℝ := fun i =>
    Function.leftLim (fun u : ℝ≥0 =>
      x + X.X u omega - rightLimit D u omega) (s i omega)
  let g : ℕ → ℝ := fun i =>
    X.X (t i omega) omega - X.X (s i omega) omega -
      (((t i omega : ℝ) - (s i omega : ℝ)) * X.c)
  let R : ℕ → ℝ := fun i =>
    (w (z i + g i) -
      taylorWithinEval w 1 (Set.uIcc (z i) (z i + g i))
        (z i) (z i + g i) -
      (iteratedDeriv 2 w (z i) * (g i) ^ 2) / 2)
  change (∑ i ∈ S, R i) =
    (∑ i ∈ S.filter (fun i => g i ≠ 0), R i)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : g i = 0
  · simp [h, R, taylorWithinEval_self]
  · simp [h]
