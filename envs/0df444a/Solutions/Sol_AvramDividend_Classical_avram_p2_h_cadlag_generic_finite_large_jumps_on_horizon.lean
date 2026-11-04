-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:36:32.539069+00:00
-- url     : https://prove2.me/submissions/ab250165-e14f-4abb-8fff-e9731decf45b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_jumpmark_vanish_from_left
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_jumpmark_vanish_from_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Actual jumps of any cadlag path exceeding a positive threshold form
a finite set on a compact nonnegative time horizon, including near zero. -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      δ ≤ dist (Y u - Function.leftLim Y u) 0}.Finite := by
  let mark : ℝ≥0 → ℝ := fun u => Y u - Function.leftLim Y u
  let S : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧ δ ≤ dist (mark u) 0}
  change S.Finite
  by_contra hfinite
  have hinf : S.Infinite := hfinite
  have hsubset : S ⊆ Set.Icc (0 : ℝ≥0) T := by
    intro u hu
    exact ⟨le_of_lt hu.1, hu.2.1⟩
  obtain ⟨a, haK, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact isCompact_Icc hsubset
  have hRight : {u : ℝ≥0 | dist (mark u) 0 < δ} ∈ (𝓝[>] a) :=
    (Metric.tendsto_nhds.mp
      (avram_p2_h_cadlag_generic_jumpmark_vanish_from_right Y hR hL a)) δ hδ
  obtain ⟨UR, hUR, hURsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hRight
  by_cases ha0 : a = 0
  · obtain ⟨y, hy, hneq⟩ :=
      (accPt_iff_nhds.mp hacc) UR hUR
    rcases hy with ⟨hyUR, hyS⟩
    have hypos : 0 < y := hyS.1
    have hsmall : dist (mark y) 0 < δ :=
      hURsub ⟨hyUR, by simpa [ha0] using hypos⟩
    exact (not_le_of_gt hsmall) hyS.2.2
  · have ha_pos : 0 < a := lt_of_le_of_ne
      (zero_le : (0 : ℝ≥0) ≤ a) (Ne.symm ha0)
    have hLeft : {u : ℝ≥0 | dist (mark u) 0 < δ} ∈ (𝓝[<] a) :=
      (Metric.tendsto_nhds.mp
        (avram_p2_h_cadlag_generic_jumpmark_vanish_from_left Y hL a ha_pos))
          δ hδ
    obtain ⟨UL, hUL, hULsub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hLeft
    obtain ⟨y, hy, hneq⟩ :=
      (accPt_iff_nhds.mp hacc) (UR ∩ UL) (inter_mem hUR hUL)
    rcases hy with ⟨hyU, hyS⟩
    rcases lt_or_gt_of_ne hneq with hya | hay
    · have hsmall : dist (mark y) 0 < δ :=
        hULsub ⟨hyU.2, hya⟩
      exact (not_le_of_gt hsmall) hyS.2.2
    · have hsmall : dist (mark y) 0 < δ :=
        hURsub ⟨hyU.1, hay⟩
      exact (not_le_of_gt hsmall) hyS.2.2
