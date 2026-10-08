-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_real_rightLim_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:50:11.930976+00:00
-- url     : https://prove2.me/submissions/52f1a5f2-8101-493b-b0a3-c5737f04c113

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℝ) :
    Measurable (fun ω =>
      Function.rightLim (fun s : ℝ => D s.toNNReal ω) r) := by
  let s : ℕ → ℝ := fun n => r + 1 / ((n : ℝ) + 1)
  have hs_nhds : Tendsto s atTop (𝓝 r) := by
    dsimp [s]
    simpa using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hs_right : Tendsto s atTop (𝓝[>] r) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within s hs_nhds
    filter_upwards [] with n
    dsimp [s]
    simp only [mem_Ioi]
    have hpos : 0 < (1 / ((n : ℝ) + 1)) := by positivity
    linarith
  have hmeas : ∀ n, Measurable (fun ω => D (s n).toNNReal ω) := by
    intro n
    exact hD.2.2.2.measurable
  apply measurable_of_tendsto_metrizable hmeas
  rw [tendsto_pi_nhds]
  intro ω
  have hmono : Monotone (fun u : ℝ => D u.toNNReal ω) :=
    (hD.2.1 ω).comp Real.toNNReal_monotone
  exact (hmono.tendsto_rightLim r).comp hs_right
