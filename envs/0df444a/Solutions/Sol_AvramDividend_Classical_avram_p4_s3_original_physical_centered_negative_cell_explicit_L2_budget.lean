-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_physical_centered_negative_cell_explicit_L2_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:21:22.583846+00:00
-- url     : https://prove2.me/submissions/369308e1-0183-4715-ad2f-8c765b5db704

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Quantitative original physical centred-count L² budget without factorial premises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1)))) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ :=
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    let R : ℝ :=
      ((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
    (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) ≤
      2 * (R ^ 2 + R) + 2 * r ^ 2 := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  let R : ℝ := ((T : ℝ≥0∞) *
    X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
  change Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
    (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) ≤
      2 * (R ^ 2 + R) + 2 * r ^ 2
  have hN2 := avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
    X T cut s t hst htT B hB hCut
  have hCentered : MemLp (fun ω => (N ω).toReal - r) 2 P :=
    avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
      X T cut s t hst htT B hB hCut
  have hCenter2 : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P :=
    (memLp_two_iff_integrable_sq hCentered.aestronglyMeasurable).1 hCentered
  have hMajorant : Integrable (fun ω =>
      2 * (N ω).toReal ^ 2 + 2 * r ^ 2) P :=
    (hN2.1.const_mul 2).add (integrable_const _)
  have hBoundPoint (ω : Ω) :
      ((N ω).toReal - r) ^ 2 ≤
        2 * (N ω).toReal ^ 2 + 2 * r ^ 2 := by
    nlinarith [sq_nonneg ((N ω).toReal + r)]
  constructor
  · exact hCenter2
  · have hI := integral_mono_ae hCenter2 hMajorant
      (Filter.Eventually.of_forall hBoundPoint)
    have hEval : (∫ ω, 2 * (N ω).toReal ^ 2 + 2 * r ^ 2 ∂P) =
        2 * (∫ ω, (N ω).toReal ^ 2 ∂P) + 2 * r ^ 2 := by
      have hScale : (∫ ω, 2 * (N ω).toReal ^ 2 ∂P) =
          2 * (∫ ω, (N ω).toReal ^ 2 ∂P) := by
        simp only [integral_const_mul, smul_eq_mul]
      have hConst : (∫ _ : Ω, (2 * r ^ 2 : ℝ) ∂P) = 2 * r ^ 2 := by
        simp
      rw [integral_add (hN2.1.const_mul 2) (integrable_const _)]
      rw [hScale, hConst]
    rw [hEval] at hI
    nlinarith [hN2.2]
