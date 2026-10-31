-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:37:03.563142+00:00
-- url     : https://prove2.me/submissions/9834c900-0c22-45f0-b9a9-d08218877530

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology MeasureTheory
open scoped NNReal

/-- A strongly adapted process with finite strict-left limits has a strongly
adapted left-limit modification, using only the original filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : StronglyAdapted 𝓕 Z)
    (hleft : ∀ ω (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Tendsto (fun s => Z s ω) (𝓝[<] t) (𝓝 l)) :
    StronglyAdapted 𝓕
      (fun t ω => Function.leftLim (fun s => Z s ω) t) := by
  intro t
  by_cases ht : t = 0
  · subst t
    change StronglyMeasurable[𝓕 0]
      (fun ω => Function.leftLim (fun s => Z s ω) (0 : ℝ≥0))
    have hEq : (fun ω => Function.leftLim (fun s => Z s ω) (0 : ℝ≥0)) =
        (fun ω => Z 0 ω) := by
      funext ω
      exact leftLim_eq_of_isBot (isBot_bot : IsBot (0 : ℝ≥0))
    rw [hEq]
    exact hZ 0
  · change StronglyMeasurable[𝓕 t]
      (fun ω => Function.leftLim (fun s => Z s ω) t)
    letI : MeasurableSpace Ω := 𝓕 t
    have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    have hstrong (n : ℕ) : StronglyMeasurable[𝓕 t]
        (fun ω => Z (t - t / ((n : ℝ≥0) + 2)) ω) := by
      exact (hZ _).mono (𝓕.mono (tsub_le_self))
    have hlim : StronglyMeasurable[𝓕 t]
        (fun ω => Filter.limUnder atTop
          (fun n : ℕ => Z (t - t / ((n : ℝ≥0) + 2)) ω)) :=
      StronglyMeasurable.limUnder hstrong
    have hdiv : Tendsto (fun n : ℕ => t / ((n : ℝ≥0) + 2))
        atTop (𝓝 0) := by
      convert (tendsto_add_atTop_iff_nat 2).2
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ≥0) t) using 1
      ext n
      norm_num [Nat.cast_add]
    have hT : Tendsto (fun n : ℕ => t - t / ((n : ℝ≥0) + 2))
        atTop (𝓝 t) := by
      have hc : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
      simpa only [tsub_zero] using hc.sub hdiv
    have hclock : Tendsto (fun n : ℕ => t - t / ((n : ℝ≥0) + 2))
        atTop (𝓝[<] t) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hT, ?_⟩
      exact Filter.Eventually.of_forall fun n => by
        have hp : 0 < t / ((n : ℝ≥0) + 2) := by positivity
        exact tsub_lt_self htpos hp
    haveI : (𝓝[<] t).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    have hEq (ω : Ω) :
        Function.leftLim (fun s => Z s ω) t =
          Filter.limUnder atTop
            (fun n : ℕ => Z (t - t / ((n : ℝ≥0) + 2)) ω) := by
      obtain ⟨l, hl⟩ := hleft ω t htpos
      exact (leftLim_eq_of_tendsto hl).trans
        ((hl.comp hclock).limUnder_eq).symm
    have hfun : (fun ω => Function.leftLim (fun s => Z s ω) t) =
        (fun ω => Filter.limUnder atTop
          (fun n : ℕ => Z (t - t / ((n : ℝ≥0) + 2)) ω)) :=
      funext hEq
    rw [hfun]
    exact hlim
