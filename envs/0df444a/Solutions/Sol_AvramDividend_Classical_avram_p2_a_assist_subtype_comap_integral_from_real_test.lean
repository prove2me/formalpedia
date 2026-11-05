-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_subtype_comap_integral_from_real_test
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:58:49.077599+00:00
-- url     : https://prove2.me/submissions/38e4719a-d374-4d3c-9117-16289fae2c99

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped ENNReal

/-- A supported real compact test has the same integral as its negative-subtype comap test. -/
theorem solution
    (μ : Measure ℝ)
    (f : {x : ℝ // x < 0} → ℝ)
    (g : ℝ → ℝ)
    (hgsupp : tsupport g ⊆ Iio (0 : ℝ))
    (hagree : ∀ x : {x : ℝ // x < 0}, g (x : ℝ) = f x) :
    (∫ x, f x ∂(Measure.comap (Subtype.val : {x : ℝ // x < 0} → ℝ) μ)) =
      (∫ y, g y ∂μ) := by
  let e : {x : ℝ // x < 0} → ℝ := Subtype.val
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Iio
  have hrange : Set.range e = Iio (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hMap :
      (∫ y, g y ∂(μ.restrict (Iio (0 : ℝ)))) =
      (∫ x, g (e x) ∂(Measure.comap e μ)) := by
    simpa only [he.map_comap, hrange] using
      (he.integral_map (μ := Measure.comap e μ) g)
  have hZero (y : ℝ) (hy : ¬ y < 0) : g y = 0 := by
    by_contra hne
    have hs : y ∈ tsupport g := subset_closure hne
    exact hy (hgsupp hs)
  have hIndicator : (Iio (0 : ℝ)).indicator g = g := by
    funext y
    by_cases hy : y < 0
    · have hyMem : y ∈ Iio (0 : ℝ) := hy
      exact Set.indicator_of_mem
        (s := Iio (0 : ℝ)) (a := y) hyMem g
    · have hyNotMem : y ∉ Iio (0 : ℝ) := hy
      calc
        (Iio (0 : ℝ)).indicator g y = 0 :=
          Set.indicator_of_notMem
            (s := Iio (0 : ℝ)) (a := y) hyNotMem g
        _ = g y := (hZero y hy).symm
  have hRestrict :
      (∫ y, g y ∂(μ.restrict (Iio (0 : ℝ)))) = (∫ y, g y ∂μ) := by
    calc
      _ = (∫ y, (Iio (0 : ℝ)).indicator g y ∂μ) :=
        (integral_indicator measurableSet_Iio).symm
      _ = (∫ y, g y ∂μ) := by rw [hIndicator]
  calc
    (∫ x, f x ∂(Measure.comap e μ)) =
        (∫ x, g (e x) ∂(Measure.comap e μ)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact (hagree x).symm
    _ = (∫ y, g y ∂(μ.restrict (Iio (0 : ℝ)))) := hMap.symm
    _ = (∫ y, g y ∂μ) := hRestrict
