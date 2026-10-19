-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_rightLimit_zero_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:19:39.866988+00:00
-- url     : https://prove2.me/submissions/03b4cc1a-8067-4840-80ec-dc1d3b149e46

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

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
    (hD : IsAdmissibleLe X 0 0 D) (ω : Ω) :
    rightLimit D 0 ω = 0 := by
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  have hmono : Monotone (fun t => D t ω) := hD.1.1.2.1 ω
  have hlo : 0 ≤ rightLimit D 0 ω := by
    haveI : Nonempty (Ioi (0 : ℝ≥0)) := ⟨⟨1, by norm_num⟩⟩
    unfold rightLimit
    refine le_ciInf fun s => ?_
    have h := hmono (show (0 : ℝ≥0) ≤ (s : ℝ≥0) from bot_le)
    simpa [hD0] using h
  have hadm := hD.1.2 ω (0 : ℝ≥0) (Or.inl rfl)
  have hhi : rightLimit D 0 ω ≤ 0 := by
    simpa [riskProcess, hD0, X.X_zero ω] using hadm
  exact le_antisymm hhi hlo
