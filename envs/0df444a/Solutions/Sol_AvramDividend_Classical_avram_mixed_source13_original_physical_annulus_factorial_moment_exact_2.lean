-- Prove2me | solution 2 for AvramDividend.Classical.avram_mixed_source13_original_physical_annulus_factorial_moment_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:54:33.062372+00:00
-- url     : https://prove2.me/submissions/7dc3c4ab-ed23-49d1-8685-8a43180601ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_uniform_grid_factorial_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- The source-exact finite-grid sandwich squeezes the factorial expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 := by
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  let R : ℝ := ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((m : ℝ) + 1))))).toReal
  let E : ℝ := ∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧ E = r ^ 2
  obtain ⟨hInt, hSand⟩ :=
    avram_mixed_source13_original_annulus_uniform_grid_factorial_sandwich X T n m hnm
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P at hInt
  have hBounds (k : ℕ) :
      r ^ 2 * (1 - 1 / ((k + 1 : ℕ) : ℝ)) ≤ E ∧
      E ≤ r ^ 2 * (1 - 1 / ((k + 1 : ℕ) : ℝ)) +
        R ^ 2 / ((k + 1 : ℕ) : ℝ) := by
    simpa [B, N, r, R, E] using hSand k
  have hInv : Tendsto (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat)
  have hLower : Tendsto
      (fun k : ℕ => r ^ 2 * (1 - 1 / ((k + 1 : ℕ) : ℝ)))
      atTop (𝓝 (r ^ 2)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => r ^ 2) atTop (𝓝 (r ^ 2))).mul
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hInv))
  have hErr : Tendsto
      (fun k : ℕ => R ^ 2 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => R ^ 2) atTop (𝓝 (R ^ 2))).mul hInv)
  have hUpper : Tendsto
      (fun k : ℕ => r ^ 2 * (1 - 1 / ((k + 1 : ℕ) : ℝ)) +
        R ^ 2 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 (r ^ 2)) := by
    simpa using hLower.add hErr
  have hLe : r ^ 2 ≤ E :=
    le_of_tendsto hLower (Filter.Eventually.of_forall fun k => (hBounds k).1)
  have hGe : E ≤ r ^ 2 :=
    ge_of_tendsto hUpper (Filter.Eventually.of_forall fun k => (hBounds k).2)
  exact ⟨hInt, le_antisymm hGe hLe⟩
