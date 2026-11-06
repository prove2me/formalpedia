-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:37:53.991673+00:00
-- url     : https://prove2.me/submissions/6ab87c93-6aff-4e87-8c5e-26cd18ad506c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_tsum_finite_support
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_mark_integrable_of_ae_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original large negative jumps have integrable signed marks on every
finite horizon, with the mark bound derived from actual source jump times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Iic (-1 : ℝ)
    IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) E N := by
  intro j N E
  classical
  obtain ⟨F, hF, _⟩ :=
    avram_p4_h_gaussian_original_largejump_tsum_finite_support X ω T
  let C : ℝ := ∑ u ∈ F, ‖j u‖
  have hC : ∀ u ∈ F, ‖j u‖ ≤ C := by
    intro u hu
    exact Finset.single_le_sum (fun v hv => norm_nonneg (j v)) hu
  let B : Set ℝ := {z | z ≤ -1 ∧ C < ‖z‖}
  have hB : MeasurableSet B := by
    change MeasurableSet
      (Iic (-1 : ℝ) ∩ ((fun z : ℝ => ‖z‖) ⁻¹' Ioi C))
    exact measurableSet_Iic.inter
      (measurableSet_Ioi.preimage continuous_norm.measurable)
  have hNo : {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧
      u ≤ T ∧ j u ≠ 0 ∧ j u ∈ B} = ∅ := by
    ext u
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    intro hu
    rcases hu with ⟨hu0, _, huT, _, huB⟩
    change j u ≤ -1 ∧ C < ‖j u‖ at huB
    exact (not_lt_of_ge (hC u ((hF u).mpr
      ⟨hu0, huT, huB.1⟩))) huB.2
  have hCount : N (Ioc (0 : ℝ≥0) T ×ˢ B) = 0 := by
    have hrect :=
      avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
        X ω 0 T B hB
    change N (Ioc (0 : ℝ≥0) T ×ˢ B) =
      ({u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧
        u ≤ T ∧ j u ≠ 0 ∧ j u ∈ B}).encard at hrect
    rw [hNo] at hrect
    simpa using hrect
  have hBadSet : {p : ℝ≥0 × ℝ | C < ‖p.2‖} ∩ E =
      Ioc (0 : ℝ≥0) T ×ˢ B := by
    ext p
    simp only [E, B, mem_inter_iff, mem_setOf_eq,
      mem_prod, mem_Ioc, mem_Iic]
    tauto
  have hMeasBad : MeasurableSet
      {p : ℝ≥0 × ℝ | C < ‖p.2‖} := by
    change MeasurableSet
      ((fun p : ℝ≥0 × ℝ => ‖p.2‖) ⁻¹' Ioi C)
    exact measurableSet_Ioi.preimage
      (continuous_norm.measurable.comp measurable_snd)
  have hBad : (N.restrict E)
      {p : ℝ≥0 × ℝ | C < ‖p.2‖} = 0 := by
    rw [Measure.restrict_apply hMeasBad]
    rw [hBadSet]
    exact hCount
  have hAe : ∀ᵐ p ∂(N.restrict E), ‖p.2‖ ≤ C := by
    have hAe' : ∀ᵐ p ∂(N.restrict E), ¬ C < ‖p.2‖ := by
      apply ae_iff.mpr
      simpa only [not_not] using hBad
    filter_upwards [hAe'] with p hp
    exact le_of_not_gt hp
  exact avram_p4_h_gaussian_original_largeband_mark_integrable_of_ae_bound
    X ω T C hAe
