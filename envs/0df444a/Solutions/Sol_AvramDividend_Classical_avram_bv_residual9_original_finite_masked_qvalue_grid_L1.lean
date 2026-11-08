-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_finite_masked_qvalue_grid_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:03:38.981852+00:00
-- url     : https://prove2.me/submissions/6357af52-41c4-44a9-b7a7-1aec454066f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_masked_qvalue_cell_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact finite physical sum of strict interior masked discounted q*w(Z)
cells is L1, for every stopped physical grid bounded by T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (C : ℝ≥0∞)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i ∈ Finset.range (n + 1), u n i ≤ T) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        (let Z : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (u n i)
         if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z ∧ ENNReal.ofReal Z < C then
           Real.exp (-(q * (u n i : ℝ))) * (q * w Z)
         else 0) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))) P := by
  let V (i : ℕ) (ω : Ω) : ℝ :=
    let Z : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (u n i)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ ENNReal.ofReal Z < C then
      Real.exp (-(q * (u n i : ℝ))) * (q * w Z)
    else 0
  have hV (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      Integrable (V i) P :=
    avram_bv_residual9_original_masked_qvalue_cell_L1
      X hBV q w hw_cont hw_neg x D hD T (u n i) (hu i hi) C
  have hSum : Integrable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        V i ω * ((u n (i + 1) : ℝ) - (u n i : ℝ))) P := by
    apply integrable_finset_sum
    intro i hi
    exact (hV i hi).mul_const _
  exact hSum
