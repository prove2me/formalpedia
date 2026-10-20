-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_rightLimit_adapted_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:08:37.239109+00:00
-- url     : https://prove2.me/submissions/20ba65c9-09b9-4096-8445-ee653ec7c42f

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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Adapted 𝓕.rightCont (fun t ω => rightLimit D t ω) := by
  intro t
  haveI : NeBot (𝓝[>] t) :=
    nhdsGT_neBot_of_exists_gt
      ⟨t + 1, lt_add_of_pos_right t zero_lt_one⟩
  have hfuture (u : ℝ≥0) (htu : t < u) :
      Measurable[𝓕 u] (fun ω => rightLimit D t ω) := by
    letI : MeasurableSpace Ω := 𝓕 u
    obtain ⟨v, hv⟩ := Filter.exists_seq_tendsto (𝓝[>] t)
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.1 (hv.eventually (Ioc_mem_nhdsGT htu))
    have hb (n : ℕ) : t < v (n + N) ∧ v (n + N) ≤ u := by
      have hn : N ≤ n + N := by omega
      exact hN (n + N) hn
    have hmeas (n : ℕ) :
        Measurable[𝓕 u] (fun ω => D (v (n + N)) ω) :=
      (hD.2.2.2 (v (n + N))).mono (𝓕.mono (hb n).2) le_rfl
    have hconv : Tendsto (fun n ω => D (v (n + N)) ω) atTop
        (𝓝 (fun ω => rightLimit D t ω)) := by
      rw [tendsto_pi_nhds]
      intro ω
      have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.2.1 ω
      have hright :
          Function.rightLim (fun s : ℝ≥0 => D s ω) t =
            rightLimit D t ω := by
        have hinf :
            Function.rightLim (fun s : ℝ≥0 => D s ω) t =
              sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) :=
          hmono.rightLim_eq_sInf
        unfold rightLimit
        calc
          Function.rightLim (fun s : ℝ≥0 => D s ω) t =
              sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) := hinf
          _ = ⨅ s : Ioi t, D s.1 ω := by
            simp only [iInf, Set.image_eq_range]
      have hlim :=
        (hmono.tendsto_rightLim t).comp
          (hv.comp (Filter.tendsto_add_atTop_nat N))
      rw [hright] at hlim
      exact hlim
    exact measurable_of_tendsto_metrizable hmeas hconv
  change Measurable[𝓕.rightCont t] (fun ω => rightLimit D t ω)
  intro S hS
  rw [𝓕.rightCont_apply, if_pos (inferInstance : NeBot (𝓝[>] t))]
  rw [MeasurableSpace.measurableSet_iInf]
  intro u
  rw [MeasurableSpace.measurableSet_iInf]
  intro hu
  exact (hfuture u hu) hS
