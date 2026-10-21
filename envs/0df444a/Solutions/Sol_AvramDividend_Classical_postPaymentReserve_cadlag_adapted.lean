-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_cadlag_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:21:43.465349+00:00
-- url     : https://prove2.me/submissions/d74cb9ec-1a24-41c2-8bb6-da33b0a5c4f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_has_leftLimits
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    (∀ ω t, ContinuousWithinAt
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (Ici t) t) ∧
    (∀ ω t, 0 < t → ∃ l : ℝ, Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (𝓝[<] t) (𝓝 l)) ∧
    Adapted 𝓕.rightCont
      (fun t ω => x + X.X t ω - rightLimit D t ω) := by
  constructor
  · intro ω t
    have hcX := X.rightCont ω t
    have hcD :=
      dividendStrategy_rightLimit_rightContinuous D hD ω t
    exact (continuousWithinAt_const.add hcX).sub hcD
  constructor
  · intro ω t ht
    obtain ⟨lX, hX⟩ := X.leftLim ω t ht
    obtain ⟨lD, hDlim⟩ :=
      dividendStrategy_rightLimit_has_leftLimits D hD ω t ht
    exact ⟨x + lX - lD, (tendsto_const_nhds.add hX).sub hDlim⟩
  intro t
  have hX : Measurable[𝓕.rightCont t] (fun ω => X.X t ω) :=
    (X.adapted t).mono (𝓕.le_rightCont t) le_rfl
  have hDpost : Measurable[𝓕.rightCont t]
      (fun ω => rightLimit D t ω) :=
    dividendStrategy_rightLimit_adapted_rightCont D hD t
  exact (measurable_const.add hX).sub hDpost
