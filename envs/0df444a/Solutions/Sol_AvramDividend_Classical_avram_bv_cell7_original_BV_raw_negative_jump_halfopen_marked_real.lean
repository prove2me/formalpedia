-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_raw_negative_jump_halfopen_marked_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:28:16.603687+00:00
-- url     : https://prove2.me/submissions/3d6e0549-85c3-448b-a716-8c29ba935da7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- On each actual original Lévy path, the BV raw negative-jump
    real sum is exactly its intrinsic half-open marked jump integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      let Δ : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      let Nst : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc s t)).map
            (fun u : ℝ≥0 => (u, Δ u)))
      (∫⁻ p, ENNReal.ofReal (-p.2) ∂Nst).toReal =
        ∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0 := by
  filter_upwards
    [AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
      X hBV] with ω hω
  intro s t hst
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
  let Nst : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict
      ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc s t)).map
        (fun u : ℝ≥0 => (u, Δ u)))
  have hCount : (∫⁻ p, ENNReal.ofReal (-p.2) ∂Nst) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ Δ u ≠ 0) ∧ u ∈ Ioc s t then
          ENNReal.ofReal (-Δ u) else 0 := by
    simpa only [Nst, Δ] using
      (AvramDividend.Classical.avram_p3_2_original_halfopen_physical_signed_jump_count_tsum
        X ω s t (fun p : ℝ≥0 × ℝ => -p.2) measurable_snd.neg).1
  have hTerms :
      (∑' u : ℝ≥0,
        if (0 < u ∧ Δ u ≠ 0) ∧ u ∈ Ioc s t then
          ENNReal.ofReal (-Δ u) else 0) =
      ∑' u : ℝ≥0,
        if s < u ∧ u ≤ t then ENNReal.ofReal (-Δ u) else 0 := by
    apply tsum_congr
    intro u
    by_cases hsu : s < u
    · by_cases hut : u ≤ t
      · have hu0 : 0 < u :=
          lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hsu
        by_cases hΔ : Δ u = 0
        · simp [hsu, hut, hu0, hΔ, Set.mem_Ioc]
        · simp [hsu, hut, hu0, hΔ, Set.mem_Ioc]
      · simp [hsu, hut, Set.mem_Ioc]
    · simp [hsu, Set.mem_Ioc]
  calc
    (∫⁻ p, ENNReal.ofReal (-p.2) ∂Nst).toReal =
        (∑' u : ℝ≥0,
          if (0 < u ∧ Δ u ≠ 0) ∧ u ∈ Ioc s t then
            ENNReal.ofReal (-Δ u) else 0).toReal :=
              congrArg ENNReal.toReal hCount
    _ = (∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then ENNReal.ofReal (-Δ u) else 0).toReal :=
              congrArg ENNReal.toReal hTerms
    _ = ∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0 := by
            simpa only [Δ, neg_sub] using (hω s t hst).2
