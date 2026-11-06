-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_e_original_physical_grid_isometry_l2_integrability_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:51:51.74281+00:00
-- url     : https://prove2.me/submissions/7ccb37ae-63b3-41ed-bd0a-3b8b0701c56a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_bounded_complete_integrability
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact physical-grid L² isometry with bounded weights and all count L² hypotheses derived. -/
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
    (hν : ∀ i, X.ν (B i) < ⊤)
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
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by
  have hHInf (i : ℕ) : MemLp (H i) ⊤ P :=
    MemLp.of_bound (hHL2 i).aestronglyMeasurable L
      (Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using hBound i ω))
  have hCountL2 (i : ℕ) :
      MemLp (fun ω => (N i ω).toReal - r i) 2 P := by
    rw [hActual i, hRate i]
    exact avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
      X T cut (grid i) (grid (i + 1)) (hGrid i)
      (hTime (i + 1)) (B i) (hB i) (hCut i)
  exact avram_p4_g_isometry_original_finite_grid_bounded_complete_integrability
    X grid hGrid ε hε B hB hBand hν N hActual r hRate
      H D hD hH hHInf hPrefix hCountL2 hSecond n
