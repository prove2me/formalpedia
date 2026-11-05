-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_subinterval_band_count_finite_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:07:31.617924+00:00
-- url     : https://prove2.me/submissions/0efe1d92-efb1-4b42-82d4-a8ad27a02c5a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T s t : ℝ≥0) (hst : t ≤ T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    ((F.filter (fun u => s < u ∧ u ≤ t)).card : ℝ≥0∞) := by
  classical
  dsimp only
  let S : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((n : ℝ) + 1))}
  have hFull :=
    avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  have hFin : S.Finite := hFull.subset (by
    intro u hu
    exact ⟨hu.1, le_trans hu.2.2.1 hst, hu.2.2.2⟩)
  have hSet : {u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈
        Iic (-(1 / ((n : ℝ) + 1)))} = S := by
    ext u
    constructor
    · rintro ⟨hu0, hsu, hut, _, hm⟩
      exact ⟨hu0, hsu, hut, hm⟩
    · rintro ⟨hu0, hsu, hut, hm⟩
      refine ⟨hu0, hsu, hut, ?_, hm⟩
      intro hz
      have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [hz] at hm
      linarith
  have hRect :=
    avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω s t (Iic (-(1 / ((n : ℝ) + 1)))) measurableSet_Iic
  rw [hSet] at hRect
  have hFilter : hFin.toFinset =
      hFull.toFinset.filter (fun u => s < u ∧ u ≤ t) := by
    ext u
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hu0, hsu, hut, hm⟩
      exact ⟨⟨hu0, le_trans hut hst, hm⟩, hsu, hut⟩
    · rintro ⟨⟨hu0, _, hm⟩, hsu, hut⟩
      exact ⟨hu0, hsu, hut, hm⟩
  calc
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
        (hFin.toFinset.card : ℝ≥0∞) := by
          rw [hRect]
          exact_mod_cast hFin.encard_eq_coe_toFinset_card
    _ = ((hFull.toFinset.filter (fun u => s < u ∧ u ≤ t)).card : ℝ≥0∞) := by
      rw [hFilter]
