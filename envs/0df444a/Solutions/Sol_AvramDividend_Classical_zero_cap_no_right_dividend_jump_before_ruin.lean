-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_no_right_dividend_jump_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:52:20.885862+00:00
-- url     : https://prove2.me/submissions/56c4cdac-8d4b-4367-a5d4-75694af467df

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_control_eq_levy_before_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (t : ℝ≥0) (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ruinTime X 0 D ω) :
    rightLimit D t ω = D t ω := by
  have hpath : D t ω = X.X t ω :=
    zero_cap_control_eq_levy_before_ruin X D hD ω t ht0 ht
  have hrisk : riskProcess X 0 D t ω = 0 := by
    simp [riskProcess, hpath]
  have hpayment : rightLimit D t ω - D t ω ≤ 0 := by
    have h := hD.1.2 ω t (Or.inr ht)
    simpa [hrisk] using h
  have hmono : Monotone (fun s => D s ω) := hD.1.1.2.1 ω
  have hnonneg : D t ω ≤ rightLimit D t ω := by
    have hbound : ∀ s : Ioi t, D t ω ≤ D s ω := by
      intro s
      exact hmono (le_of_lt s.property)
    letI : Nonempty (Ioi t) := by
      obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, t < s := exists_gt t
      exact ⟨⟨s, hs⟩⟩
    change D t ω ≤ (⨅ s : Ioi t, D s ω)
    exact le_ciInf hbound
  linarith
