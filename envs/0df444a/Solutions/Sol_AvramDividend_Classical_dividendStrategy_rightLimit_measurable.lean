-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_rightLimit_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:42:09.777387+00:00
-- url     : https://prove2.me/submissions/20ceefdb-3133-4eb0-bd98-38ea9f538ff9

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
    (t : ℝ≥0) :
    Measurable (fun ω => rightLimit D t ω) := by
  let s : ℕ → ℝ≥0 := fun n => t + 1 / ((n : ℝ≥0) + 1)
  have hs_nhds : Tendsto s atTop (𝓝 t) := by
    dsimp [s]
    simpa using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)))
  have hs_right : Tendsto s atTop (𝓝[>] t) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within s hs_nhds
    filter_upwards [] with n
    dsimp [s]
    simp only [mem_Ioi]
    have hpos : 0 < (1 / ((n : ℝ≥0) + 1)) := by positivity
    exact lt_add_of_pos_right t hpos
  have hmeas : ∀ n, Measurable (fun ω => D (s n) ω) := by
    intro n
    exact hD.2.2.2.measurable
  apply measurable_of_tendsto_metrizable hmeas
  rw [tendsto_pi_nhds]
  intro ω
  have hmono : Monotone (fun u : ℝ≥0 => D u ω) := hD.2.1 ω
  have hright :
      Function.rightLim (fun u : ℝ≥0 => D u ω) t =
        rightLimit D t ω := by
    have hinf :
        Function.rightLim (fun u : ℝ≥0 => D u ω) t =
          sInf ((fun u : ℝ≥0 => D u ω) '' Ioi t) :=
      hmono.rightLim_eq_sInf
    unfold rightLimit
    calc
      Function.rightLim (fun u : ℝ≥0 => D u ω) t =
          sInf ((fun u : ℝ≥0 => D u ω) '' Ioi t) := hinf
      _ = ⨅ u : Ioi t, D u.1 ω := by
        simp only [iInf, Set.image_eq_range]
  have hlim :=
    (hmono.tendsto_rightLim t).comp hs_right
  rw [hright] at hlim
  exact hlim
