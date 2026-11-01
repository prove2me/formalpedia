-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_jump_measure_rectangle_encard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:07:02.386174+00:00
-- url     : https://prove2.me/submissions/fab45254-6b57-424e-ac1a-9cd58edfbfd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- The actual original postpayment marked-jump measure evaluates each
Borel time-and-mark rectangle by the extended count of precisely the
positive-time combined Lévy and dividend jumps within that rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        ((x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)))
      (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      ((X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
        (rightLimit D u ω - D u ω)) ≠ 0 ∧
      ((X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
        (rightLimit D u ω - D u ω)) ∈ B}).encard := by
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
  have hrect : MeasurableSet (Ioc s t ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hpre : MeasurableSet ((fun u : ℝ≥0 => (u, j u)) ⁻¹' (Ioc s t ×ˢ B)) :=
    hrect.preimage hF
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
    (fun u => (u, j u))) (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧ j u ≠ 0 ∧ j u ∈ B}).encard
  rw [Measure.map_apply hF hrect]
  rw [Measure.restrict_apply hpre]
  rw [Measure.count_apply (hpre.inter hS)]
  apply congrArg (fun T : Set ℝ≥0 => (T.encard : ℝ≥0∞))
  ext u
  simp [Set.mem_prod, Set.mem_preimage, Set.mem_inter_iff, j,
    and_assoc, and_left_comm, and_comm]
