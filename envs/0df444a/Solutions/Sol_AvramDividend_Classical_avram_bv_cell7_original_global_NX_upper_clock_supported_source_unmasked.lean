-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:34:25.197682+00:00
-- url     : https://prove2.me/submissions/c4ba1d13-ad2f-418f-8117-93c104dcebde

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- On the original global Lévy jump measure, a marked source with true
    upper-clock support has its exact time restriction automatically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s : ℝ≥0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F)
    (hSupport : ∀ p : ℝ≥0 × ℝ, s < p.1 → F p = 0) :
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    (∫⁻ p, F p ∂NX) =
      (∫⁻ p, (if p.1 ∈ Ioc 0 s then F p else 0) ∂NX) := by
  classical
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
      (fun v : ℝ≥0 => (v, Δ v)))
  have hAll : (∫⁻ p, F p ∂NX) =
      ∑' v : ℝ≥0,
        if 0 < v ∧ Δ v ≠ 0 then F (v, Δ v) else 0 := by
    simpa only [NX, Δ, Set.mem_univ, and_true, ite_true] using
      (AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
        X ω Set.univ MeasurableSet.univ F hF)
  have hCut :
      (∫⁻ p, (if p.1 ∈ Ioc 0 s then F p else 0) ∂NX) =
      ∑' v : ℝ≥0,
        if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 s then
          F (v, Δ v) else 0 := by
    simpa only [NX, Δ] using
      (AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
        X ω (Ioc 0 s) measurableSet_Ioc F hF)
  have hTerms :
      (∑' v : ℝ≥0,
        if 0 < v ∧ Δ v ≠ 0 then F (v, Δ v) else 0) =
      ∑' v : ℝ≥0,
        if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 s then
          F (v, Δ v) else 0 := by
    apply tsum_congr
    intro v
    by_cases hj : 0 < v ∧ Δ v ≠ 0
    · by_cases hvs : v ≤ s
      · simp [hj, hj.1, hvs, Set.mem_Ioc]
      · have hf : F (v, Δ v) = 0 :=
          hSupport (v, Δ v) (lt_of_not_ge hvs)
        simp [hj, hvs, hf, Set.mem_Ioc]
    · simp [hj]
  exact hAll.trans (hTerms.trans hCut.symm)
