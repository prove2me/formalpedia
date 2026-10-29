-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_dyadic_cauchy_stationary_v2_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:28:41.807239+00:00
-- url     : https://prove2.me/submissions/6a2a515d-8eb6-4f68-a73a-0825ddfd4817

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_bv_cauchyseq_real_event_measurable_ws01c
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (s : ℝ≥0) :
    P {ω | CauchySeq (fun n : ℕ =>
      X.drift -
        (X.X (s + ((1 : ℝ≥0) / 2) ^ n) ω - X.X s ω) /
          (((1 : ℝ≥0) / 2) ^ n : ℝ))} =
    P {ω | CauchySeq (fun n : ℕ =>
      X.drift -
        (X.X (((1 : ℝ≥0) / 2) ^ n) ω - X.X 0 ω) /
          (((1 : ℝ≥0) / 2) ^ n : ℝ))} := by
  set A : Set (ℝ≥0 → ℝ) := {f | CauchySeq (fun n : ℕ =>
      X.drift - (f (((1 : ℝ≥0) / 2) ^ n) - f 0) / (((1 : ℝ≥0) / 2) ^ n : ℝ))} with hA
  have hAm : MeasurableSet A :=
    bv_cauchyseq_real_event_measurable_ws01c _ fun n => by
      refine measurable_const.sub (Measurable.div_const ?_ _)
      exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  have hshift : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) :=
    levy_finiteStopping_stoppedFuturePath_measurable X (fun _ => s) (isStoppingTime_const _ _)
  have hpath := levy_wholePath_measurable X
  have h1 : {ω | CauchySeq (fun n : ℕ =>
      X.drift - (X.X (s + ((1 : ℝ≥0) / 2) ^ n) ω - X.X s ω) / (((1 : ℝ≥0) / 2) ^ n : ℝ))} =
      (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) ⁻¹' A := by
    ext ω; simp [hA]
  have h2 : {ω | CauchySeq (fun n : ℕ =>
      X.drift - (X.X (((1 : ℝ≥0) / 2) ^ n) ω - X.X 0 ω) / (((1 : ℝ≥0) / 2) ^ n : ℝ))} =
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) ⁻¹' A := by
    ext ω; simp [hA]
  rw [h1, h2, ← Measure.map_apply hshift hAm, ← Measure.map_apply hpath hAm,
    levy_shiftedFuturePath_stationary_law X s]
