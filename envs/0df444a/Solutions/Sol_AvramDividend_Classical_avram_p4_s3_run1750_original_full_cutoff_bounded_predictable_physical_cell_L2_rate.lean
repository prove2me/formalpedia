-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_bounded_predictable_physical_cell_L2_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:09:26.672441+00:00
-- url     : https://prove2.me/submissions/ef38734a-c630-4d6c-8aee-5c4d67f66518

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact physical full-cutoff cell with bounded predictable L² rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (cut : ℕ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hL : 0 ≤ L) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω, (H ω * ((N ω).toReal - r))^2 ∂P) ≤ r * L^2 := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
  change (∫ ω, (H ω * ((N ω).toReal-r))^2 ∂P) ≤ r * L^2
  have hIso :=
    (avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
      X s T cut H hH L hBound).2
  change (∫ ω, (H ω * ((N ω).toReal-r))^2 ∂P) =
    r * ∫ ω, (H ω)^2 ∂P at hIso
  rw [hIso]
  have hGlobalSM : StronglyMeasurable H :=
    hH.mono (𝓕.rightCont.le s)
  have hLp : MemLp H 2 P :=
    MemLp.of_bound hGlobalSM.aestronglyMeasurable L
      (Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using hBound ω))
  have hBdd (ω : Ω) : (H ω)^2 ≤ L^2 := by
    have hprod : 0 ≤ (L - |H ω|) * (L + |H ω|) :=
      mul_nonneg (sub_nonneg.mpr (hBound ω))
        (add_nonneg hL (abs_nonneg _))
    nlinarith [sq_abs (H ω)]
  have hle := integral_mono (hLp.integrable_sq)
    (integrable_const (L^2)) hBdd
  have hIntBound : (∫ ω, (H ω)^2 ∂P) ≤ L^2 := by
    simpa using hle
  exact mul_le_mul_of_nonneg_left hIntBound ENNReal.toReal_nonneg
