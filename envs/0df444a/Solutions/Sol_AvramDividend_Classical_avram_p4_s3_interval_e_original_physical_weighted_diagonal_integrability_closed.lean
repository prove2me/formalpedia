-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_e_original_physical_weighted_diagonal_integrability_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:51:55.859982+00:00
-- url     : https://prove2.me/submissions/9c15adef-ef11-4d88-bccc-2915853d969f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_centered_negative_cell_explicit_L2_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original predictable weighted Poisson-cell diagonal with all L2 side conditions discharged. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ)
    (hRate : r =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)
    (hSecond : P[(fun ω => ((N ω).toReal - r) ^ 2)
      | 𝓕 s] =ᵐ[P] (fun _ => r))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by
  subst N
  subst r
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
    r * ∫ ω, (H ω) ^ 2 ∂P
  have hCount :=
    avram_p4_s3_original_physical_centered_negative_cell_explicit_L2_budget
      X T cut s t hst htT B hB hCut
  have hWeighted :=
    avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto
      X T cut s t hst htT ε hε B hB hBand hCut
      H hH hHL2 L hBound
  have hHSq : Integrable (fun ω => (H ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hHL2.aestronglyMeasurable).1 hHL2
  have hWSq0 : Integrable (fun ω =>
      (H ω * ((N ω).toReal - r)) ^ 2) P :=
    (memLp_two_iff_integrable_sq hWeighted.1.aestronglyMeasurable).1
      hWeighted.1
  have hWSq : Integrable (fun ω =>
      (H ω) ^ 2 * ((N ω).toReal - r) ^ 2) P := by
    convert hWSq0 using 1
    ext ω
    ring
  exact avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
    X s t hst ε hε B hB hBand hν N rfl r rfl
      hSecond H hH hCount.1 hHSq hWSq
