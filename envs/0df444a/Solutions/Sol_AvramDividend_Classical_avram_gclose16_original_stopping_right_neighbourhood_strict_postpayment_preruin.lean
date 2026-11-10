-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose16_original_stopping_right_neighbourhood_strict_postpayment_preruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:33:43.165268+00:00
-- url     : https://prove2.me/submissions/577d6328-09d8-4912-ad53-6beb0d47cf0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A pre-ruin genuine stopping clock admits a positive right neighbourhood
of the actual postpayment reserve, on a common almost-sure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P,
      (τ ω : ℝ≥0∞) < ruinTime X x D ω →
      ∀ᶠ s in 𝓝[Set.Ici (τ ω)] (τ ω),
        0 < x + X.X s ω - rightLimit D s ω := by
  filter_upwards [
    avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
      X hBV x C D hD τ hτ hstop
  ] with ω hstrict
  intro hbefore
  have hcont :
      ContinuousWithinAt
        (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω)
        (Set.Ici (τ ω)) (τ ω) :=
    avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous
      X x D hD.1.1 ω (τ ω)
  have hmem :
      Set.Ioi (0 : ℝ) ∈
        𝓝 (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) :=
    isOpen_Ioi.mem_nhds (hstrict hbefore)
  exact hcont.eventually hmem
