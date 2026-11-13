-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_simple_bounded_mark_pathwise_fibre_partition_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:59:25.708072+00:00
-- url     : https://prove2.me/submissions/68ad0adb-1a85-467c-a2b8-9d5eaeec9405

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_real_simple_mark_integral_partition_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original physical bounded Borel simple mark integral equals its true
disjoint fibre count sum pathwise almost everywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ᵐ ω ∂P,
      (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) =
        ∑ y ∈ g.range, y *
          (NX ω (Ioc 0 T ×ˢ (S ∩ g ⁻¹' {y}))).toReal := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let A : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ S
  have hA : MeasurableSet A := measurableSet_Ioc.prod hS
  have hSub : A ⊆ Ioc 0 T ×ˢ Iio (0 : ℝ) :=
    Set.prod_mono (Subset.rfl) hNeg
  have hMeas : Measurable (fun p : ℝ≥0 × ℝ => g p.2) :=
    g.measurable.comp measurable_snd
  have hOrig := avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
    X hFinite
  filter_upwards [hOrig] with ω hω
  have hMass : NX ω A < ⊤ :=
    lt_of_le_of_lt (measure_mono hSub) (hω T)
  have hgMeas : AEStronglyMeasurable
      (fun p : ℝ≥0 × ℝ => g p.2) ((NX ω).restrict A) :=
    hMeas.aestronglyMeasurable
  have hgBound : ∀ᵐ p ∂((NX ω).restrict A), ‖g p.2‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem hA] with p hp
    simpa only [Real.norm_eq_abs] using hBound p.2 hp.2
  have hgInt : IntegrableOn
      (fun p : ℝ≥0 × ℝ => g p.2) A (NX ω) :=
    IntegrableOn.of_bound hMass hgMeas 1 hgBound
  exact avram_a20_real_simple_mark_integral_partition_exact
    (NX ω) T S hS g hgInt
