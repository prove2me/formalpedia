-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_joint_real_cauchy_event_meas_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:53:40.364034+00:00
-- url     : https://prove2.me/submissions/8e2dd907-4834-455d-a382-5750955c9a27

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_bv_real_toNNReal_measurable_explicit_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_cauchyseq_real_event_measurable_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology Set
open scoped NNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) :
    MeasurableSet {z : ℝ × Ω |
      CauchySeq (fun n : ℕ =>
        X.drift -
          (X.X (Real.toNNReal z.1 + ((1 : ℝ≥0) / 2) ^ n) z.2 -
            X.X (Real.toNNReal z.1) z.2) /
              (((1 : ℝ≥0) / 2) ^ n : ℝ))} := by
  let v : ℕ → ℝ × Ω → ℝ := fun n z =>
    X.drift -
      (X.X (Real.toNNReal z.1 + ((1 : ℝ≥0) / 2) ^ n) z.2 -
        X.X (Real.toNNReal z.1) z.2) /
          (((1 : ℝ≥0) / 2) ^ n : ℝ)
  have hToNNReal : Measurable (Real.toNNReal : ℝ → ℝ≥0) :=
    bv_real_toNNReal_measurable_explicit_ws01c
  have hTime : Measurable
      (fun z : ℝ × Ω => Real.toNNReal z.1) :=
    hToNNReal.comp measurable_fst
  have hJoint := chat04_levy_joint_time_state_measurable X
  have hv (n : ℕ) : Measurable (v n) := by
    have hTimeShift : Measurable
        (fun z : ℝ × Ω =>
          Real.toNNReal z.1 + ((1 : ℝ≥0) / 2) ^ n) :=
      hTime.add_const _
    have hShift : Measurable (fun z : ℝ × Ω =>
        X.X (Real.toNNReal z.1 + ((1 : ℝ≥0) / 2) ^ n) z.2) :=
      hJoint.comp (hTimeShift.prodMk measurable_snd)
    have hBase : Measurable (fun z : ℝ × Ω =>
        X.X (Real.toNNReal z.1) z.2) :=
      hJoint.comp (hTime.prodMk measurable_snd)
    exact measurable_const.sub ((hShift.sub hBase).div_const _)
  change MeasurableSet {z : ℝ × Ω | CauchySeq (fun n => v n z)}
  exact bv_cauchyseq_real_event_measurable_ws01c v hv
