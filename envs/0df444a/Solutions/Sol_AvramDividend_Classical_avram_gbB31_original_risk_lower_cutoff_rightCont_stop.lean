-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB31_original_risk_lower_cutoff_rightCont_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:37:12.337506+00:00
-- url     : https://prove2.me/submissions/4319035c-f4fc-43e5-b13a-26a4d7433bfb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_generic_capped_closed_hit_isStoppingTime
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hRiskCont : ∀ ω, Continuous
      (fun t : ℝ≥0 => riskProcess X x D t ω))
    (S : Set ℝ≥0) (hS : S.Countable)
    (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (H : ℝ≥0) (b : ℝ) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun t : ℝ≥0 => -(riskProcess X x D t ω)) ⁻¹'
          Ici (-b)) ∪ {H}))) := by 
  let U : ℝ≥0 → Ω → ℝ :=
    fun t ω => -(riskProcess X x D t ω)
  have hAdaptRisk := riskProcess_adapted X x D hD
  have hAdaptU : Adapted 𝓕 U := by
    intro t
    exact (hAdaptRisk t).neg
  have hContU : ∀ ω, Continuous (fun t => U t ω) := by
    intro ω
    exact (hRiskCont ω).neg
  have hRight : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun u => U u ω) (Ici t) t := by
    intro ω t
    exact (hContU ω).continuousWithinAt
  have hUSC : ∀ ω (t : ℝ≥0),
      UpperSemicontinuousOn (fun u => U u ω) (Icc 0 t) := by
    intro ω t
    exact (hContU ω).continuousOn.upperSemicontinuousOn
  have hStop :=
    avram_gbB31_generic_capped_closed_hit_isStoppingTime
      U hAdaptU hRight hUSC S hS hDense h0 H (-b)
  intro t
  exact ((MeasurableSpace.le_def).mp
    ((Filtration.le_rightCont 𝓕) t)) _ (hStop t)
