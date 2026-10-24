-- Prove2me | solution 1 for AvramDividend.Classical.finite_time_state_future_product_of_cylinders
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:07:30.34709+00:00
-- url     : https://prove2.me/submissions/dadb4b89-0645-46cd-af0c-48fe29da9118

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (hFinite : ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I,
        MeasurableSpace.comap
          (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P) :
    Measure.map
      (fun ω => (H ω,
        fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P =
      (Measure.map H P).prod
        (Measure.map (fun ω => fun t : ℝ≥0 =>
          X.X (s + t) ω - X.X s ω) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s + t) ω - X.X s ω
  have hHm : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    have ht : Measurable (X.X (s + t)) :=
      (X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl
    exact ht.sub ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hFuture :
      Indep (MeasurableSpace.comap Y inferInstance) (𝓕 s) P := by
    simpa only [Y] using
      AvramDividend.Classical.chat04_whole_future_process_indep_past_of_finite_cylinders
        X s hFinite
  have hHle : MeasurableSpace.comap H inferInstance ≤ 𝓕 s := hH.comap_le
  have hIndep : Indep (MeasurableSpace.comap Y inferInstance)
      (MeasurableSpace.comap H inferInstance) P :=
    indep_of_indep_of_le_right hFuture hHle
  have hIF : IndepFun H Y P :=
    (IndepFun_iff_Indep H Y P).2 hIndep.symm
  have hProd := hIF.map_prod_eq_prod_map_map hHm.aemeasurable hYm.aemeasurable
  simpa only [Y] using hProd
