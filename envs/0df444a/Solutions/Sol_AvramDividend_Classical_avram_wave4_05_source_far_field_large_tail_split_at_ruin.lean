-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_far_field_large_tail_split_at_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:03:50.453247+00:00
-- url     : https://prove2.me/submissions/6dc53f9a-cbf0-49b5-b360-90c18038ac01

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_large_tail_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact large-jump source integral split at reserve zero; the negative reserve
boundary enters through a real tail-intensity atom rather than disappearing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    (∫ y in Iic (-1 : ℝ),
      (vcstar W (x + y) - vcstar W x) ∂X.ν) =
      X.ν.real (Iio (-x)) * (-vcstar W x) +
        ∫ y in Icc (-x) (-1 : ℝ),
          (vcstar W (x + y) - vcstar W x) ∂X.ν := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hx1 : 1 ≤ x := by dsimp [a] at *; linarith
  let f : ℝ → ℝ := fun y => vcstar W (x + y) - vcstar W x
  have hdom : IntegrableOn f (Iic (-1 : ℝ)) X.ν :=
    avram_wave4_05_source_far_field_large_tail_integrable X q W hW x hfar
  have hsub1 : Iio (-x) ⊆ Iic (-1 : ℝ) := by
    intro y hy
    change y < -x at hy
    change y ≤ -1
    linarith
  have hsub2 : Icc (-x) (-1 : ℝ) ⊆ Iic (-1 : ℝ) := by
    intro y hy
    exact hy.2
  have hi1 : IntegrableOn f (Iio (-x)) X.ν := hdom.mono_set hsub1
  have hi2 : IntegrableOn f (Icc (-x) (-1 : ℝ)) X.ν :=
    hdom.mono_set hsub2
  have hUnion : Iio (-x) ∪ Icc (-x) (-1 : ℝ) = Iic (-1 : ℝ) := by
    ext y
    constructor
    · intro hy
      rcases hy with hy | hy
      · exact hsub1 hy
      · exact hy.2
    · intro hy
      by_cases hyr : y < -x
      · exact Or.inl hyr
      · exact Or.inr ⟨le_of_not_gt hyr, hy⟩
  have hDisj : Disjoint (Iio (-x)) (Icc (-x) (-1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro y hy hz
    exact (not_lt_of_ge hz.1) hy
  have hpoint : Set.EqOn f (fun _ : ℝ => -vcstar W x) (Iio (-x)) := by
    intro y hy
    have hylt : y < -x := hy
    have hneg : x + y < 0 := by linarith
    have hv : vcstar W (x + y) = 0 := by
      change barrierValue W a (x + y) = 0
      simp [barrierValue, hneg]
    dsimp [f]
    rw [hv]
    simp
  calc
    (∫ y in Iic (-1 : ℝ), f y ∂X.ν) =
        ∫ y in Iio (-x) ∪ Icc (-x) (-1 : ℝ), f y ∂X.ν := by
      rw [hUnion]
    _ = (∫ y in Iio (-x), f y ∂X.ν) +
          ∫ y in Icc (-x) (-1 : ℝ), f y ∂X.ν :=
      setIntegral_union hDisj measurableSet_Icc hi1 hi2
    _ = X.ν.real (Iio (-x)) * (-vcstar W x) +
          ∫ y in Icc (-x) (-1 : ℝ), f y ∂X.ν := by
      rw [setIntegral_congr_fun measurableSet_Iio hpoint]
      simp
