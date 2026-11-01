-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_original_source_ruinStopped_fullStieltjes_randomPayoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:33:13.565094+00:00
-- url     : https://prove2.me/submissions/f9f88830-efd6-4996-8893-2bca272f39b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (θ q T : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t : ℝ, if t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T then
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) -
            (t.toNNReal : ℝ) * q)) else 0
      ∂dividendMeasure D ω) := by
  let τ : Ω → ℝ≥0∞ := ruinTime X x D
  let S : Set (ℝ × Ω) :=
    {z | z.1 ∈ paymentTimes (τ z.2) ∩ Iic T}
  have hτ : Measurable τ := ruinTime_measurable X x D hD
  have ht : Measurable (fun z : ℝ × Ω => ENNReal.ofReal z.1) :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have hr : Measurable (fun z : ℝ × Ω => τ z.2) :=
    hτ.comp measurable_snd
  have hS : MeasurableSet S := by
    have hzero : MeasurableSet {z : ℝ × Ω | z.1 = 0} := by
      exact (measurable_fst : Measurable (fun z : ℝ × Ω => z.1))
        (measurableSet_singleton (0 : ℝ) : MeasurableSet ({(0 : ℝ)} : Set ℝ))
    have hfirst : MeasurableSet {z : ℝ × Ω | 0 ≤ z.1} :=
      measurableSet_le measurable_const measurable_fst
    have hpre : MeasurableSet {z : ℝ × Ω | ENNReal.ofReal z.1 < τ z.2} :=
      measurableSet_lt ht hr
    have hend : MeasurableSet {z : ℝ × Ω | z.1 ≤ T} :=
      measurableSet_le measurable_fst measurable_const
    change MeasurableSet {z : ℝ × Ω |
      z.1 ∈ paymentTimes (τ z.2) ∩ Iic T}
    simp only [paymentTimes, Set.mem_inter_iff, Set.mem_Iic, Set.mem_setOf_eq]
    exact (hfirst.inter (hzero.union hpre)).inter hend
  have h :=
    avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
      X x D hD θ q S hS
  simpa only [S, τ, Set.mem_setOf_eq] using h
