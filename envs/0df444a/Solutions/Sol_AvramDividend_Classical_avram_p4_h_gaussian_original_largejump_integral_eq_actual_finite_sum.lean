-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:55:46.038175+00:00
-- url     : https://prove2.me/submissions/136a2363-02d2-4953-b82b-293b9b461a55

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_source_tsum_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_tsum_finite_support
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original Jlarge is exactly the finite sum of its own large negative jumps
on each bounded horizon, with no extra integrability or source law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ j u ≤ -1) ∧
      avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω =
        ∑ u ∈ F, j u := by
  intro j
  classical
  obtain ⟨F, hF, hsum⟩ :=
    avram_p4_h_gaussian_original_largejump_tsum_finite_support X ω T
  let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Iic (-1 : ℝ)
  have hpath :=
    avram_p4_h_gaussian_original_largejump_integral_eq_source_tsum_unconditional
      X ω T
  change avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω =
    ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
      E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0 at hpath
  have hterm : ∀ u : ℝ≥0,
      (if 0 < u ∧ j u ≠ 0 then
        E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0) =
      (if 0 < u ∧ u ≤ T then
        (if j u ≤ -1 then j u else 0) else 0) := by
    intro u
    by_cases hu0 : 0 < u
    · by_cases huT : u ≤ T
      · by_cases hneg : j u ≤ -1
        · have hnz : j u ≠ 0 := by linarith
          simp [E, Set.indicator, Set.mem_prod, hu0, huT, hneg, hnz]
        · simp [E, Set.indicator, Set.mem_prod, hu0, huT, hneg]
      · simp [E, Set.indicator, Set.mem_prod, hu0, huT]
    · simp [hu0]
  refine ⟨F, hF, ?_⟩
  calc
    avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω =
        ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
          E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0 := hpath
    _ = ∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then
        (if j u ≤ -1 then j u else 0) else 0 :=
      tsum_congr hterm
    _ = ∑ u ∈ F, j u := hsum
