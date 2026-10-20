-- Prove2me | solution 1 for AvramDividend.Classical.levy_indepIncrements_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:32:08.160976+00:00
-- url     : https://prove2.me/submissions/c7c17fef-4c15-4ec1-b575-bdda438afd77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_indep_from_sequence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance)
      (𝓕.rightCont s) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  by_cases heq : s = t
  · subst t
    simpa only [sub_self, MeasurableSpace.comap_const] using
      (ProbabilityTheory.indep_bot_left (𝓕.rightCont s) :
        Indep (⊥ : MeasurableSpace Ω) (𝓕.rightCont s) P)
  · have hlt : s < t := lt_of_le_of_ne hst heq
    haveI : NeBot (𝓝[>] s) :=
      nhdsGT_neBot_of_exists_gt ⟨t, hlt⟩
    obtain ⟨v, hv⟩ := Filter.exists_seq_tendsto (𝓝[>] s)
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.1 (hv.eventually (Ioc_mem_nhdsGT hlt))
    have hb (n : ℕ) : s < v (n + N) ∧ v (n + N) ≤ t := by
      have hn : N ≤ n + N := by omega
      exact hN (n + N) hn
    exact levy_rightCont_indep_from_sequence X s t
      (fun n => v (n + N))
      (fun n => (hb n).1) (fun n => (hb n).2)
      (hv.comp (Filter.tendsto_add_atTop_nat N))
