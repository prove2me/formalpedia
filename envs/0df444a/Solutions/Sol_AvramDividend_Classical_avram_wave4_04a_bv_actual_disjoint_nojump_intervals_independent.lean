-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_disjoint_nojump_intervals_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:18:30.508096+00:00
-- url     : https://prove2.me/submissions/11ff3516-f858-4701-b370-53d2e5e8f038

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_nojump_past_factor_rightCont

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Disjoint original source-X future nojump events factor on the same space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    P ({ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc s t →
      X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0} ∩
       {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc u v →
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0}) =
      P {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc s t →
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0} *
      P {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc u v →
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0} := by
  classical
  let J₁ : Set Ω := {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc s t →
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0}
  let J₂ : Set Ω := {ω : Ω | ∀ r : ℝ≥0, r ∈ Ioc u v →
    X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r = 0}
  let B : Set Ω := {ω : Ω |
    X.X t ω - X.X s ω = ((t : ℝ) - (s : ℝ)) * X.drift}
  have hAE : J₁ =ᵐ[P] B :=
    avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
      X hBV hFinite s t hst
  have hXt := (X.adapted t).mono
    ((𝓕.mono htu).trans (𝓕.le_rightCont u)) le_rfl
  have hXs := (X.adapted s).mono
    ((𝓕.mono (hst.trans htu)).trans (𝓕.le_rightCont u)) le_rfl
  have hBMeas : @MeasurableSet Ω (𝓕.rightCont u) B := by
    change @MeasurableSet Ω (𝓕.rightCont u)
      ((fun ω : Ω => X.X t ω - X.X s ω) ⁻¹'
        {((t : ℝ) - (s : ℝ)) * X.drift})
    exact (hXt.sub hXs) (measurableSet_singleton _)
  have hFactor : P (B ∩ J₂) = P B * P J₂ :=
    avram_wave4_04a_bv_actual_nojump_past_factor_rightCont
      X hBV hFinite u v huv B hBMeas
  have hAEInter :
      (fun ω : Ω => ω ∈ J₁ ∧ ω ∈ J₂) =ᵐ[P]
      (fun ω : Ω => ω ∈ B ∧ ω ∈ J₂) := by
    filter_upwards [hAE] with ω hω
    exact congrArg (fun p : Prop => p ∧ ω ∈ J₂) hω
  change P (J₁ ∩ J₂) = P J₁ * P J₂
  calc
    P (J₁ ∩ J₂) = P (B ∩ J₂) := measure_congr hAEInter
    _ = P B * P J₂ := hFactor
    _ = P J₁ * P J₂ := by rw [measure_congr hAE]
