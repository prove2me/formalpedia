-- Prove2me | solution 3 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_grid_chronological_cross_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:03:12.170344+00:00
-- url     : https://prove2.me/submissions/d671674f-316f-49af-9045-24e70e33eba7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_cross_window_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0) (hst : ∀ i, s i ≤ t i) (n : ℕ) :
    let Jpast : Fin m → Ω → ℝ≥0∞ := fun i ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc 0 (s i) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Jfuture : Fin m → Ω → ℝ≥0∞ := fun i ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc (s i) (t i) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    (∑ i : Fin m, ∫⁻ ω, Jpast i ω * Jfuture i ω ∂P) =
      ∑ i : Fin m, (∫⁻ ω, Jpast i ω ∂P) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) *
          X.ν (Iic (-(1 / ((n : ℝ) + 1))))) := by
  dsimp only
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact avram_p4_f_assembly_original_chronological_cross_window_mean
    X (s i) (t i) (hst i) n
