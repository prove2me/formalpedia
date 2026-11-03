-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:11:42.589479+00:00
-- url     : https://prove2.me/submissions/14c4da9f-7274-4668-8240-8e1cbb84c69b

import Mathlib
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

theorem solution
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b) :
    hg.vectorMeasure.IntegrableOn (Function.leftLim f) (Ioc a b) ∧
    hg.vectorMeasure.IntegrableOn (Function.leftLim f) ({a} : Set ℝ≥0) ∧
    hf.vectorMeasure.IntegrableOn (Function.rightLim g) (Ioc a b) ∧
    hf.vectorMeasure.IntegrableOn (Function.rightLim g) ({a} : Set ℝ≥0) := by
  have hvar_finite (μ : VectorMeasure ℝ≥0 ℝ) :
      IsFiniteMeasure μ.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hmeas (u : ℝ≥0 → ℝ) (hu : BoundedVariationOn u Set.univ) :
      Measurable u := by
    obtain ⟨p, r, hp, hr, hpr⟩ :=
      hu.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
    rw [hpr]
    have hpmono : Monotone p := by
      intro x y hxy
      exact hp (by simp) (by simp) hxy
    have hrmono : Monotone r := by
      intro x y hxy
      exact hr (by simp) (by simp) hxy
    exact hpmono.measurable.sub hrmono.measurable
  have hbound (u : ℝ≥0 → ℝ) (hu : BoundedVariationOn u Set.univ) :
      ∀ t, ‖u t‖ ≤ ‖u 0‖ + (eVariationOn u Set.univ).toReal := by
    intro t
    have hd := hu.dist_le (x := t) (y := 0) (by simp) (by simp)
    have hd' : ‖u t - u 0‖ ≤ (eVariationOn u Set.univ).toReal := by
      simpa [dist_eq_norm] using hd
    calc
      ‖u t‖ = ‖(u t - u 0) + u 0‖ := by simp
      _ ≤ ‖u t - u 0‖ + ‖u 0‖ := norm_add_le _ _
      _ ≤ ‖u 0‖ + (eVariationOn u Set.univ).toReal := by linarith
  have hInt (u : ℝ≥0 → ℝ) (hu : BoundedVariationOn u Set.univ)
      (μ : VectorMeasure ℝ≥0 ℝ) (s : Set ℝ≥0) (hs : MeasurableSet s) :
      μ.IntegrableOn u s := by
    letI : IsFiniteMeasure μ.variation := hvar_finite μ
    have hm : AEStronglyMeasurable u μ.variation :=
      (hmeas u hu).aestronglyMeasurable
    change Integrable u ((μ.restrict s).variation)
    rw [VectorMeasure.variation_restrict hs]
    apply Measure.integrableOn_of_bounded
      (M := ‖u 0‖ + (eVariationOn u Set.univ).toReal)
      (measure_ne_top _ _) hm
    exact Filter.Eventually.of_forall (hbound u hu)
  exact ⟨hInt _ hf.leftLim _ _ measurableSet_Ioc,
    hInt _ hf.leftLim _ _ (MeasurableSet.singleton a),
    hInt _ hg.rightLim _ _ measurableSet_Ioc,
    hInt _ hg.rightLim _ _ (MeasurableSet.singleton a)⟩
