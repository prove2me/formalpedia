-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_offtime_borel_count_integrable_zero_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:12:51.072119+00:00
-- url     : https://prove2.me/submissions/bd0616ef-c1f9-4af1-a4a1-88af011baa53

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual off-time Borel physical jump covariance is L1 and zero without extra source moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (n m : ℕ)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((m : ℝ) + 1)))) :
    let Jpast : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Jfuture : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let rp : ℝ :=
      ((s : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let rf : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((Jpast ω).toReal - rp) *
      ((Jfuture ω).toReal - rf)) P ∧
      ∫ ω, ((Jpast ω).toReal - rp) *
        ((Jfuture ω).toReal - rf) ∂P = 0 := by
  let Bp : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let Jpast : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ Bp)
  let Jfuture : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let rp : ℝ := ((s : ℝ≥0∞) * X.ν Bp).toReal
  let rf : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => ((Jpast ω).toReal - rp) *
    ((Jfuture ω).toReal - rf)) P ∧
    ∫ ω, ((Jpast ω).toReal - rp) *
      ((Jfuture ω).toReal - rf) ∂P = 0
  have hPm : Measurable[𝓕 s] Jpast :=
    avram_p4_f_assembly_original_past_count_raw_measurable_auto X s n
  have hPr : Measurable[𝓕 s] (fun ω => (Jpast ω).toReal) :=
    ENNReal.measurable_toReal.comp hPm
  have hPastStrong : StronglyMeasurable[𝓕 s]
      (fun ω => (Jpast ω).toReal - rp) :=
    (hPr.sub_const rp).stronglyMeasurable
  have hPastL2 : MemLp (fun ω => (Jpast ω).toReal - rp) 2 P := by
    have hSource := avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
      X s n 0 s (by simp) le_rfl Bp measurableSet_Iic Subset.rfl
    simpa only [Jpast, rp, Bp, tsub_zero] using hSource
  exact avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
    X t m s t hst le_rfl ε hε B hB hBand hCut
    (fun ω => (Jpast ω).toReal - rp) hPastStrong hPastL2
