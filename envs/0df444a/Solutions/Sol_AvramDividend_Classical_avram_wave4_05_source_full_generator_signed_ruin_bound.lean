-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_full_generator_signed_ruin_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:44:24.565906+00:00
-- url     : https://prove2.me/submissions/6995d4cf-cb82-4a92-b959-1dcd3b4f775b

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_positive_jump_part_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_landing_atom_integral_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A sharp original upper-generator residual inequality: use the exact
signed integral on every jump landing at or below zero, retain a possible
landing atom, and bound only the surviving (nonruin) jumps by zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤
        X.c + (∫ y in Ioo (-1 : ℝ) (-x),
          (-vcstar W x - y) ∂X.ν) -
        (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x +
        (X.ν).real ({-x} : Set ℝ) *
          (vcstar W 0 - vcstar W x + if x < 1 then x else 0) -
        q * vcstar W x := by
  let g : ℝ → ℝ := fun y =>
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y
  let C : Set ℝ := Iic (-x)
  let R : Set ℝ := Ioo (-x) 0
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  obtain ⟨hdom, hcross⟩ :=
    avram_wave4_05_source_ruin_landing_atom_integral_exact
      X q W hW x hx
  have hint : IntegrableOn g (Iio (0 : ℝ)) X.ν := by exact hdom
  have hCsub : C ⊆ Iio (0 : ℝ) := by
    intro y hy
    have hyle : y ≤ -x := hy
    exact lt_of_le_of_lt hyle (neg_lt_zero.mpr hx0)
  have hRsub : R ⊆ Iio (0 : ℝ) := by
    intro y hy
    exact hy.2
  have hCint : IntegrableOn g C X.ν := hint.mono_set hCsub
  have hRint : IntegrableOn g R X.ν := hint.mono_set hRsub
  have hCindicator : Integrable (C.indicator g) X.ν :=
    (integrable_indicator_iff measurableSet_Iic).mpr hCint
  have hRindicator : Integrable (R.indicator g) X.ν :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hRint
  have hpartition :
      (∫ y in Iio (0 : ℝ), g y ∂X.ν) =
        ∫ y in Iio (0 : ℝ), C.indicator g y + R.indicator g y ∂X.ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have hyneg : y < 0 := hy
    by_cases hyle : y ≤ -x
    · have hc : y ∈ C := hyle
      have hr : y ∉ R := by
        intro hr
        have hrlt : -x < y := hr.1
        linarith
      simp [Set.indicator_of_mem hc, Set.indicator_of_notMem hr]
    · have hygt : -x < y := lt_of_not_ge hyle
      have hr : y ∈ R := ⟨hygt, hyneg⟩
      have hc : y ∉ C := by
        intro hc
        have hcle : y ≤ -x := hc
        linarith
      simp [Set.indicator_of_notMem hc, Set.indicator_of_mem hr]
  have hCid :
      (∫ y in Iio (0 : ℝ), C.indicator g y ∂X.ν) =
        ∫ y in C, g y ∂X.ν := by
    rw [setIntegral_indicator measurableSet_Iic]
    rw [Set.inter_eq_right.mpr hCsub]
  have hRid :
      (∫ y in Iio (0 : ℝ), R.indicator g y ∂X.ν) =
        ∫ y in R, g y ∂X.ν := by
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [Set.inter_eq_right.mpr hRsub]
  have hRnonpos : (∫ y in R, g y ∂X.ν) ≤ 0 := by
    have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) R X.ν := by simp
    have hbound : (∫ y in R, g y ∂X.ν) ≤
        ∫ y in R, (0 : ℝ) ∂X.ν := by
      apply setIntegral_mono_on hRint hzero measurableSet_Ioo
      intro y hy
      have hyneg : y < 0 := hy.2
      have hnot : y ∉ Ioo (-1 : ℝ) (-x) := by
        intro hmem
        have hlt : -x < y := hy.1
        linarith [hmem.2]
      have heq := avram_wave4_05_source_all_cap_positive_jump_part_exact
        X hX q hq W hW x hx y hyneg
      rw [if_neg hnot] at heq
      have hle : g y ≤ max 0 (g y) := le_max_right _ _
      change max 0 (g y) = 0 at heq
      rw [heq] at hle
      exact hle
    simpa using hbound
  have hfull :
      (∫ y in Iio (0 : ℝ), g y ∂X.ν) =
        (∫ y in C, g y ∂X.ν) + (∫ y in R, g y ∂X.ν) := by
    rw [hpartition]
    rw [integral_add hCindicator.integrableOn hRindicator.integrableOn]
    rw [hCid, hRid]
  refine ⟨hdom, ?_⟩
  rw [vcstar_generator_above_eq_drift_add_jump X W x hx]
  change X.c + (∫ y in Iio (0 : ℝ), g y ∂X.ν) - q * vcstar W x ≤ _
  rw [hfull, hcross]
  linarith
