-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_bddAbove_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:32:14.35812+00:00
-- url     : https://prove2.me/submissions/25247c33-7e47-4b57-a314-a89cf663b7e3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

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
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) T =>
        x + X.X s.1 ω - rightLimit D s.1 ω)) := by
  have hr (t : ℝ≥0) :
      Tendsto (fun s => X.X s ω) (𝓝[≥] t) (𝓝 (X.X t ω)) :=
    (X.rightCont ω t).tendsto
  have hl (t : ℝ≥0) :
      ∃ l : ℝ, Tendsto (fun s => X.X s ω) (𝓝[<] t) (𝓝 l) := by
    by_cases ht : t = 0
    · subst t
      refine ⟨0, ?_⟩
      have hb : (𝓝[<] (0 : ℝ≥0)) = ⊥ :=
        nhdsLT_eq_bot_iff.mpr
          (.inl (fun v => (zero_le : (0 : ℝ≥0) ≤ v)))
      rw [hb]
      exact tendsto_bot
    · have htpos : 0 < t :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht)
      exact X.leftLim ω t htpos
  obtain ⟨M, hM⟩ :=
    one_sided_limits_bddAbove_Icc (fun s => X.X s ω) hr hl T
  refine ⟨x + M - D 0 ω, ?_⟩
  rintro z ⟨s, rfl⟩
  have hXt : X.X s.1 ω ≤ M := hM (Set.mem_range_self s)
  have hDmono : D 0 ω ≤ D s.1 ω :=
    (hD.2.1 ω) (zero_le : (0 : ℝ≥0) ≤ s.1)
  have hDright : D s.1 ω ≤ rightLimit D s.1 ω :=
    dividendStrategy_le_rightLimit D hD ω s.1
  linarith
