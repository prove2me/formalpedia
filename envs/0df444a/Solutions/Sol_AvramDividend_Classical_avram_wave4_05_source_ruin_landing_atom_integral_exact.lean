-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_ruin_landing_atom_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:35:39.906967+00:00
-- url     : https://prove2.me/submissions/1b45d1b4-4d6b-41bd-b405-402288ca2134

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_jump_integral_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact source generator contribution from all negative jumps that
land at or below reserve zero, including a possible atom at the landing
boundary. BV models may have nonzero v(0); the atom is not silently killed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      (∫ y in Iic (-x),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) =
        (∫ y in Ioo (-1 : ℝ) (-x),
          (-vcstar W x - y) ∂X.ν) -
        (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x +
        (X.ν).real ({-x} : Set ℝ) *
          (vcstar W 0 - vcstar W x + if x < 1 then x else 0) := by
  let g : ℝ → ℝ := fun y =>
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y
  let A : Set ℝ := Iio (-x)
  let B : Set ℝ := {-x}
  let C : Set ℝ := Iic (-x)
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  obtain ⟨hdom, hstrict⟩ :=
    avram_wave4_05_source_ruin_jump_integral_exact X q W hW x hx
  have hder : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x hx
  have hland : g (-x) =
      vcstar W 0 - vcstar W x + if x < 1 then x else 0 := by
    dsimp [g]
    have hzero : x + -x = 0 := by ring
    by_cases hx1 : x < 1
    · have hmem : -x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith [hx0]⟩
      unfold SpectrallyNegativeLevy.generatorIntegrand
      simp only [Set.indicator_of_mem hmem, Pi.one_apply]
      rw [hzero, hder, if_pos hx1]
      ring
    · have hnot : -x ∉ Ioo (-1 : ℝ) 1 := by
        intro hy
        exact hx1 (by linarith [hy.1])
      unfold SpectrallyNegativeLevy.generatorIntegrand
      simp only [Set.indicator_of_notMem hnot, Pi.zero_apply]
      rw [hzero, if_neg hx1]
      ring
  have hsubC : C ⊆ Iio (0 : ℝ) := by
    intro y hy
    have hyle : y ≤ -x := hy
    exact lt_of_le_of_lt hyle (neg_lt_zero.mpr hx0)
  have hsubA : A ⊆ C := by
    intro y hy
    have hylt : y < -x := hy
    exact le_of_lt hylt
  have hsubB : B ⊆ C := by
    intro y hy
    have hyeq : y = -x := hy
    change y ≤ -x
    rw [hyeq]
  have hAsub : A ⊆ Iio (0 : ℝ) := hsubA.trans hsubC
  have hBsub : B ⊆ Iio (0 : ℝ) := hsubB.trans hsubC
  have hint : IntegrableOn g (Iio (0 : ℝ)) X.ν := by
    exact hdom
  have hAint : Integrable (A.indicator g) X.ν :=
    (integrable_indicator_iff measurableSet_Iio).mpr
      (hint.mono_set hAsub)
  have hBint : Integrable (B.indicator g) X.ν :=
    (integrable_indicator_iff (measurableSet_singleton (-x))).mpr
      (hint.mono_set hBsub)
  have hpartition :
      (∫ y in C, g y ∂X.ν) =
        ∫ y in C, A.indicator g y + B.indicator g y ∂X.ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    have hle : y ≤ -x := hy
    rcases lt_or_eq_of_le hle with hlt | heq
    · have ha : y ∈ A := hlt
      have hb : y ∉ B := by
          intro hb
          have hbeq : y = -x := hb
          exact (ne_of_lt hlt) hbeq
      simp [Set.indicator_of_mem ha, Set.indicator_of_notMem hb]
    · have ha : y ∉ A := by
          intro ha
          have halt : y < -x := ha
          exact (ne_of_lt halt) heq
      have hb : y ∈ B := heq
      simp [Set.indicator_of_notMem ha, Set.indicator_of_mem hb]
  have hAeq :
      (∫ y in C, A.indicator g y ∂X.ν) = ∫ y in A, g y ∂X.ν := by
    rw [setIntegral_indicator measurableSet_Iio]
    rw [Set.inter_eq_right.mpr hsubA]
  have hBeq :
      (∫ y in C, B.indicator g y ∂X.ν) = ∫ y in B, g y ∂X.ν := by
    rw [setIntegral_indicator (measurableSet_singleton (-x))]
    rw [Set.inter_eq_right.mpr hsubB]
  have hBconst :
      (∫ y in B, g y ∂X.ν) =
        (X.ν).real B * g (-x) := by
    have heq : (∫ y in B, g y ∂X.ν) =
        ∫ y in B, g (-x) ∂X.ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_singleton (-x))] with y hy
      have : y = -x := hy
      rw [this]
    rw [heq]
    simp [setIntegral_const, mul_comm]
  refine ⟨hdom, ?_⟩
  change (∫ y in C, g y ∂X.ν) = _
  rw [hpartition]
  rw [integral_add hAint.integrableOn hBint.integrableOn]
  rw [hAeq, hBeq, hstrict, hBconst, hland]
