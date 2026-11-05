-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_original_finite_jump_test_count_integral_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:56:24.43694+00:00
-- url     : https://prove2.me/submissions/7e9bb7cf-c7be-4377-a3fb-babd36952acd

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_finite_weighted_mark_count_real_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
/-- A genuine original-process marked counting integral at a finite horizon equals the real sum over its exact finite nonzero marked-jump support. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0)
    (f : ℝ → ℝ) (hf : Measurable f) (hfpos : ∀ y, 0 ≤ f y)
    (F : Finset ℝ≥0)
    (hF : ∀ u : ℝ≥0, u ∈ F ↔
      (0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      u ∈ Ioc 0 T ∧
      f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) :
    (∫⁻ p in (Ioc 0 T ×ˢ (Set.univ : Set ℝ)),
      ENNReal.ofReal (f p.2) ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ENNReal.ofReal (∑ u ∈ F,
        f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  let J : Set ℝ≥0 := {u | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}
  let j : ℝ≥0 → ℝ≥0 × ℝ := fun u => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let R : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ (Set.univ : Set ℝ)
  let g : ℝ≥0 × ℝ → ℝ := R.indicator (fun p => f p.2)
  have hj : Measurable j := by
    have hslice : Measurable (fun u : ℝ≥0 => (u, ω)) := measurable_id.prodMk measurable_const
    have hdelta : Measurable (fun u : ℝ≥0 =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) :=
      (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hslice
    exact measurable_id.prodMk hdelta
  have hJ : MeasurableSet J :=
    avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable X ω hj
  have hR : MeasurableSet R := measurableSet_Ioc.prod MeasurableSet.univ
  have hg : Measurable g := (hf.comp measurable_snd).indicator hR
  have hgpos : ∀ p, 0 ≤ g p := by
    intro p
    by_cases hp : p ∈ R
    · simpa [g, Set.indicator_of_mem hp] using hfpos p.2
    · simp [g, Set.indicator_of_notMem hp]
  have hF' : ∀ u, u ∈ F ↔ u ∈ J ∧ g (j u) ≠ 0 := by
    intro u
    constructor
    · intro hu
      rcases (hF u).1 hu with ⟨hju, ht, hv⟩
      refine ⟨hju, ?_⟩
      simpa [g, j, R, ht] using hv
    · rintro ⟨hju, hgv⟩
      have ht : u ∈ Ioc 0 T := by
        by_contra hnot
        have hz : g (j u) = 0 := by simp [g, j, R, hnot]
        exact hgv hz
      have hv : f (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0 := by
        simpa [g, j, R, ht] using hgv
      exact (hF u).2 ⟨hju, ht, hv⟩
  have hfin := avram_p2_a_assist_finite_weighted_mark_count_real_sum
    J hJ j hj g hg hgpos F hF'
  calc
    (∫⁻ p in R, ENNReal.ofReal (f p.2) ∂((Measure.count.restrict J).map j)) =
        (∫⁻ p, ENNReal.ofReal (g p) ∂((Measure.count.restrict J).map j)) := by
          rw [← lintegral_indicator hR]
          congr 1
          funext p
          by_cases hp : p ∈ R <;> simp [g, hp]
    _ = ENNReal.ofReal (∑ u ∈ F, g (j u)) := hfin
    _ = ENNReal.ofReal (∑ u ∈ F,
        f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro u hu
          have ht := ((hF u).1 hu).2.1
          simp [g, j, R, ht]
