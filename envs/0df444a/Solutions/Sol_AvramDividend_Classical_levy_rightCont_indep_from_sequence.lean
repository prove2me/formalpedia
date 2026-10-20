-- Prove2me | solution 1 for AvramDividend.Classical.levy_rightCont_indep_from_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T18:07:05.752448+00:00
-- url     : https://prove2.me/submissions/9878e2ec-bec2-4793-b5c3-c708b91fc9cd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_future_increment_indep_rightCont_prior
import Theorems.Thm_AvramDividend_Classical_levy_increment_right_limit
import Theorems.Thm_AvramDividend_Classical_independence_of_ambient_pointwise_limit_real
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0)
    (u : ℕ → ℝ≥0) (hsu : ∀ n, s < u n)
    (hut : ∀ n, u n ≤ t)
    (hlim : Tendsto u atTop (𝓝[>] s)) :
    Indep
      (MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance)
      (𝓕.rightCont s) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hXt : Measurable[mΩ] (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hXu (n : ℕ) : Measurable[mΩ] (X.X (u n)) :=
    (X.adapted (u n)).mono (𝓕.le (u n)) le_rfl
  have hZ (n : ℕ) :
      Measurable[mΩ] (fun ω => X.X t ω - X.X (u n) ω) :=
    hXt.sub (hXu n)
  have hz : Measurable[mΩ] (fun ω => X.X t ω - X.X s ω) :=
    hXt.sub ((X.adapted s).mono (𝓕.le s) le_rfl)
  exact independence_of_ambient_pointwise_limit_real
    (𝓕.rightCont.le s)
    (fun n ω => X.X t ω - X.X (u n) ω)
    (fun ω => X.X t ω - X.X s ω)
    hZ hz
    (fun n => levy_future_increment_indep_rightCont_prior
      X s (u n) t (hsu n) (hut n))
    (fun ω => (levy_increment_right_limit X ω s t).comp hlim)
