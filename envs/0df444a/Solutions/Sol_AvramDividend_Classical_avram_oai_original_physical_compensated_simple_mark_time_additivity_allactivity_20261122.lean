-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_compensated_simple_mark_time_additivity_allactivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:03:12.316768+00:00
-- url     : https://prove2.me/submissions/e726899d-b999-488f-a967-70f449c073e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_negative_mark_real_count_interval_additivity_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_finite_time_mark_real_compensator_additivity_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤) (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let F : ℝ≥0 → Ω → ℝ := fun u ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc 0 u ×ˢ B y)).toReal -
          (((u : ℝ≥0∞) * X.ν (B y))).toReal)
    let G : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal)
    ∀ᵐ ω ∂P, F t ω = F s ω + G ω  := by
  classical
  intro NX B F G
  have hBm : ∀ y ∈ g.range, MeasurableSet (B y) := by
    intro y hy
    exact hS.inter (g.measurable (measurableSet_singleton y))
  have hBn : ∀ y ∈ g.range, B y ⊆ Iio (0 : ℝ) := by
    intro y hy z hz
    exact hNeg hz.1
  have hBν : ∀ y ∈ g.range, X.ν (B y) < ⊤ := by
    intro y hy
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hν
  have hAll : ∀ᵐ ω ∂P, ∀ y ∈ g.range,
      (NX ω (Ioc 0 t ×ˢ B y)).toReal =
        (NX ω (Ioc 0 s ×ˢ B y)).toReal +
          (NX ω (Ioc s t ×ˢ B y)).toReal := by
    apply (Filter.eventually_all_finset g.range).2
    intro y hy
    simpa only [NX] using
      (avram_oai_original_negative_mark_real_count_interval_additivity_allactivity_20261122
        X 0 s t (by exact zero_le) hst
          (B y) (hBm y hy) (hBn y hy) (hBν y hy))
  filter_upwards [hAll] with ω hω
  change (∑ y ∈ g.range, y *
      ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
        (((t : ℝ≥0∞) * X.ν (B y))).toReal)) =
    (∑ y ∈ g.range, y *
      ((NX ω (Ioc 0 s ×ˢ B y)).toReal -
        (((s : ℝ≥0∞) * X.ν (B y))).toReal)) +
      (∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [hω y hy,
    avram_oai_finite_time_mark_real_compensator_additivity_20261122 s t hst (X.ν (B y))]
  ring
