-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_simple_mark_count_process_rightcont_stronglyAdapted_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:50:49.891394+00:00
-- url     : https://prove2.me/submissions/0e06e17d-e2f3-44c2-8fb6-8ec8a74495e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ) (hS : MeasurableSet S)
    (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let F : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
          (((t : ℝ≥0∞) * X.ν (B y))).toReal)
    StronglyAdapted 𝓕.rightCont F  := by
  classical
  intro NX B F
  intro t
  have hCells : ∀ y ∈ g.range, MeasurableSet (B y) := by
    intro y hy
    exact hS.inter (g.measurable (measurableSet_singleton y))
  have hSum : StronglyMeasurable[𝓕.rightCont t]
      (∑ y ∈ g.range, fun ω =>
        y * ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
          (((t : ℝ≥0∞) * X.ν (B y))).toReal)) := by
    apply Finset.stronglyMeasurable_sum
    intro y hy
    have hCount :
        StronglyMeasurable[𝓕.rightCont t]
          (fun ω => (NX ω (Ioc 0 t ×ˢ B y)).toReal) := by
      simpa only [NX] using
        (avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
          X 0 t t le_rfl (B y) (hCells y hy))
    exact stronglyMeasurable_const.mul
      (hCount.sub stronglyMeasurable_const)
  simpa only [F, NX, B, Finset.sum_fn] using hSum
