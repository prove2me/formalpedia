-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_nojump_nogaussian_drift_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:00:37.368981+00:00
-- url     : https://prove2.me/submissions/9dd3e077-7e9d-4290-861d-7ba1addfe76f

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : X.σ = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    ∀ᵐ ω ∂P,
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c = 0 := by
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  change ∀ᵐ ω ∂P, Y ω = 0
  have hm : Measurable Y :=
    avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
      X τ hτ h
  have hme : Measurable (fun ω => ENNReal.ofReal ((Y ω) ^ 2)) :=
    (hm.pow_const 2).ennreal_ofReal
  have hb : (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) ≤ 0 := by
    have he :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
        X hν τ hτ T hbounded h
    change (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) ≤
      ENNReal.ofReal ((h : ℝ) * X.σ ^ 2) at he
    simpa [hσ] using he
  have hzero : (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) = 0 :=
    le_antisymm hb bot_le
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal ((Y ω) ^ 2) = 0 :=
    (lintegral_eq_zero_iff hme).mp hzero
  filter_upwards [hae] with ω hw
  have hsq : (Y ω) ^ 2 ≤ 0 := (ENNReal.ofReal_eq_zero).mp hw
  nlinarith [sq_nonneg (Y ω)]