-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_future_borel_marked_grid_count_stationary_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:52:30.923418+00:00
-- url     : https://prove2.me/submissions/0cab51f5-3790-4e07-a3eb-c303193b6702

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    Measure.map (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        (X.X (s + grid (i + 1)) ω - X.X s ω) -
          (X.X (s + grid i) ω - X.X s ω) ∈ B)).card) P =
    Measure.map (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        X.X (grid (i + 1)) ω - X.X (grid i) ω ∈ B)).card) P := by
  classical
  let p : ℕ → (ℝ≥0 → ℝ) → Prop := fun i Y =>
    Y (grid (i + 1)) - Y (grid i) ∈ B
  have hp (i : ℕ) : MeasurableSet {Y : ℝ≥0 → ℝ | p i Y} := by
    exact hB.preimage
      ((measurable_pi_apply (grid (i + 1))).sub (measurable_pi_apply (grid i)))
  have hSum : Measurable (fun Y : ℝ≥0 → ℝ =>
      ∑ i ∈ Finset.range n, if p i Y then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hp i) measurable_const measurable_const
  have hEq :
      (fun Y : ℝ≥0 → ℝ =>
        ((Finset.range n).filter (fun i => p i Y)).card) =
      (fun Y : ℝ≥0 → ℝ =>
        ∑ i ∈ Finset.range n, if p i Y then (1 : ℕ) else 0) := by
    funext Y
    exact Finset.card_filter (fun i => p i Y) (Finset.range n)
  let Fpath : (ℝ≥0 → ℝ) → ℕ := fun Y =>
    ((Finset.range n).filter (fun i => p i Y)).card
  have hF : Measurable Fpath := by
    change Measurable (fun Y : ℝ≥0 → ℝ =>
      ((Finset.range n).filter (fun i => p i Y)).card)
    rw [hEq]
    exact hSum
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (s + t) ω - X.X s ω
  let W : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hZm : Measurable Z := by
    exact measurable_pi_lambda _ fun t =>
      (X.adapted.measurable (i := s + t)).sub
        (X.adapted.measurable (i := s))
  have hWm : Measurable W := levy_wholePath_measurable X
  have hstationary : Measure.map Z P = Measure.map W P := by
    simpa only [Z, W] using levy_shiftedFuturePath_stationary_law X s
  have hmap := congrArg (Measure.map Fpath) hstationary
  have hmapZ : Measure.map Fpath (Measure.map Z P) =
      Measure.map (Fpath ∘ Z) P := Measure.map_map hF hZm
  have hmapW : Measure.map Fpath (Measure.map W P) =
      Measure.map (Fpath ∘ W) P := Measure.map_map hF hWm
  rw [hmapZ, hmapW] at hmap
  simpa only [Fpath, p, Z, W, Function.comp_def] using hmap
