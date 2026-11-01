-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_lintegral_eq_chronological_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:59:36.172841+00:00
-- url     : https://prove2.me/submissions/20226620-6185-4865-a3a2-94adb5e8daf8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- A nonnegative kernel integrated against the actual postpayment marked
jump measure equals its chronological sum. Simultaneous source jumps and
dividend right atoms contribute their combined mark, not a Levy mark. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (f : (ℝ≥0 × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧
          ((x + X.X u ω - rightLimit D u ω) -
            Function.leftLim
              (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u) ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          (x + X.X u ω - rightLimit D u ω) -
            Function.leftLim
              (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧
      ((X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
        (rightLimit D u ω - D u ω)) ≠ 0
      then f (u,
        (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
          (rightLimit D u ω - D u ω))
      else 0 := by
  rw [avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
    X x D hD ω]
  let j : ℝ≥0 → ℝ := fun u =>
    (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
      (rightLimit D u ω - D u ω)
  let jMasked : ℝ≥0 → ℝ := fun u => if 0 < u then j u else 0
  have hMasked : Measurable jMasked := by
    exact (avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable
      X x D hD).comp
      (Measurable.prodMk measurable_id measurable_const)
  have hException :
      {u : ℝ≥0 | jMasked u ≠ j u} ⊆ {(0 : ℝ≥0)} := by
    intro u hu
    by_cases hz : u = 0
    · simp [hz]
    · exfalso
      have hp : (0 : ℝ≥0) < u := pos_iff_ne_zero.mpr hz
      exact hu (by simp [jMasked, hp])
  have hj : Measurable j :=
    hMasked.measurable_of_countable_ne
      ((Set.countable_singleton (0 : ℝ≥0)).mono hException)
  have hpos : MeasurableSet {u : ℝ≥0 | 0 < u} :=
    measurableSet_lt measurable_const measurable_id
  have hnonzero : MeasurableSet {u : ℝ≥0 | j u ≠ 0} :=
    (measurableSet_eq_fun hj measurable_const).compl
  have hS : MeasurableSet {u : ℝ≥0 | 0 < u ∧ j u ≠ 0} :=
    hpos.inter hnonzero
  have hF : Measurable (fun u : ℝ≥0 => (u, j u)) :=
    Measurable.prodMk measurable_id hj
  change (∫⁻ p, f p ∂
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then f (u, j u) else 0
  rw [lintegral_map hf hF]
  rw [← lintegral_indicator hS (fun u : ℝ≥0 => f (u, j u))]
  rw [lintegral_count]
  apply tsum_congr
  intro u
  by_cases hu : 0 < u ∧ j u ≠ 0
  · simp [Set.indicator, hu]
  · simp [Set.indicator, hu]
