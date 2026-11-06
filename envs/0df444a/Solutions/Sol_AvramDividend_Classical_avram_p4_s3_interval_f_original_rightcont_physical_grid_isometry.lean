-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_f_original_rightcont_physical_grid_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:33:04.782201+00:00
-- url     : https://prove2.me/submissions/a956608c-a725-4f36-a8ae-c0732338151b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_physical_grid_isometry_l2_integrability_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hFinite : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕.rightCont (grid i)] =ᵐ[P] (fun _ => r i))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by
  obtain ⟨Y, hYX, hc, hσ, hνEq⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hActualY : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ Y.X u ω -
          Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          Y.X u ω - Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i) := by
    intro i
    simpa only [hYX] using hActual i
  have hFiniteY : ∀ i, Y.ν (B i) < ⊤ := by
    intro i
    simpa only [hνEq] using hFinite i
  have hRateY : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * Y.ν (B i)).toReal := by
    intro i
    simpa only [hνEq] using hRate i
  exact avram_p4_s3_interval_e_original_physical_grid_isometry_l2_integrability_auto
    Y T cut grid hGrid hTime ε hε B hB hBand hCut hFiniteY
    N hActualY r hRateY H D hD hH hHL2 L hBound hPrefix hSecond n
