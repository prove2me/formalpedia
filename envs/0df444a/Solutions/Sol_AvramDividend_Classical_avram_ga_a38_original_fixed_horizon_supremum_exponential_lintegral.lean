-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a38_original_fixed_horizon_supremum_exponential_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:35:48.307202+00:00
-- url     : https://prove2.me/submissions/58510a8c-8016-4926-afee-f0dc4f383c59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a36_clock_tail_integrability_transfer
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (nu : Measure ℝ) [SFinite nu]
    (n : ℝ≥0) (β : ℝ) (hβ : 0 ≤ β)
    (hTail : 0 < nu (Set.Ioi (n : ℝ)))
    (hMoment : (∫⁻ z : Ω×ℝ,
      ENNReal.ofReal (Real.exp
        (β * runningSup X (Real.toNNReal z.2) z.1))
          ∂ (P.prod nu)) < ⊤) :
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (β * runningSup X n ω))
        ∂ P) < ⊤ := by
  have hPair : Measurable (fun ω : Ω => (n, ω)) :=
    Measurable.prod measurable_const measurable_id
  have hSup : Measurable (fun ω : Ω => runningSup X n ω) :=
    (levy_runningSup_joint_time_path_measurable X).comp hPair
  have hg : Measurable (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (β * runningSup X n ω))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hSup))
  apply avram_ga_a36_clock_tail_integrability_transfer
    P nu (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (β * runningSup X n ω)))
    (fun z : Ω×ℝ =>
      ENNReal.ofReal (Real.exp
        (β * runningSup X (Real.toNNReal z.2) z.1)))
    (n : ℝ) hg hTail
  · intro z hz
    have hTime : n ≤ Real.toNNReal z.2 := by
      have ht : (n : ℝ) ≤ z.2 := le_of_lt hz
      simpa using (Real.toNNReal_mono ht)
    have hSupLe : runningSup X n z.1 ≤
        runningSup X (Real.toNNReal z.2) z.1 :=
      (runningSup_monotone_and_path_le X z.1).1 hTime
    have hMul : β * runningSup X n z.1 ≤
        β * runningSup X (Real.toNNReal z.2) z.1 :=
      mul_le_mul_of_nonneg_left hSupLe hβ
    exact ENNReal.ofReal_le_ofReal ((Real.exp_le_exp).2 hMul)
  · exact hMoment
