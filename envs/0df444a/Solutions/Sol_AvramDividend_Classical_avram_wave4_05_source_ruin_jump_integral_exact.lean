-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_ruin_jump_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:20:06.78973+00:00
-- url     : https://prove2.me/submissions/0b302241-f4d7-4b2b-9197-49ffbbf13373

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The *signed* source generator integral over all strict ruin-causing
negative jumps is exactly the small-jump compensation crossing integral
minus the finite intensity of uncompensated large ruin jumps. This treats
the Lévy atom at a jump landing exactly on zero correctly, by excluding it. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      (∫ y in Iio (-x),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) =
        (∫ y in Ioo (-1 : ℝ) (-x),
          (-vcstar W x - y) ∂X.ν) -
        (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x := by
  let S : Set ℝ := Ioo (-1 : ℝ) (-x)
  let L : Set ℝ := Iic (-1 : ℝ) ∩ Iio (-x)
  let J : ℝ → ℝ := S.indicator (fun y : ℝ => -vcstar W x - y)
  let K : ℝ → ℝ := L.indicator (fun _ : ℝ => vcstar W x)
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  have hdom := vcstar_generatorIntegrable_strictly_above_real_cstar
    X q W hW x hx
  have hder : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x hx
  have hSsub : S ⊆ Iic (-x) := by
    intro y hy
    exact le_of_lt hy.2
  have hLsub : L ⊆ Iic (-x) := by
    intro y hy
    have hylt : y < -x := hy.2
    exact le_of_lt hylt
  have hmass : X.ν (Iic (-x)) < ⊤ :=
    levy_negative_mass_away_from_zero_finite X x hx0
  have hSfin : X.ν S < ⊤ := lt_of_le_of_lt (measure_mono hSsub) hmass
  have hLfin : X.ν L < ⊤ := lt_of_le_of_lt (measure_mono hLsub) hmass
  have hSconst : IntegrableOn (fun y : ℝ => -vcstar W x - y) S X.ν := by
    refine IntegrableOn.of_bound hSfin (by fun_prop) (|vcstar W x| + 1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hyabs : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1],
      by linarith [hy.2, hx0]⟩
    calc
      ‖-vcstar W x - y‖ = |vcstar W x + y| := by
        rw [Real.norm_eq_abs]
        rw [show -vcstar W x - y = -(vcstar W x + y) by ring, abs_neg]
      _ ≤ |vcstar W x| + |y| := abs_add_le _ _
      _ ≤ |vcstar W x| + 1 := by linarith
  have hLconst : IntegrableOn (fun _ : ℝ => vcstar W x) L X.ν := by
    refine IntegrableOn.of_bound hLfin (by fun_prop) |vcstar W x| ?_
    exact Filter.Eventually.of_forall (fun y => by
      simp [Real.norm_eq_abs])
  have hj : Integrable J X.ν :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hSconst
  have hk : Integrable K X.ν :=
    (integrable_indicator_iff (measurableSet_Iic.inter measurableSet_Iio)).mpr hLconst
  have hpoint : ∀ y ∈ Iio (-x),
      SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y =
        J y - K y := by
    intro y hy
    have hylt : y < -x := hy
    have hxy : x + y < 0 := by linarith
    have hzero : vcstar W (x + y) = 0 := by
      change barrierValue W (cstar W).toReal (x + y) = 0
      simp [barrierValue, hxy]
    by_cases hlarge : y ≤ -1
    · have hL : y ∈ L := ⟨hlarge, hy⟩
      have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
        intro hz
        exact (not_lt_of_ge hlarge) hz.1
      have hnotS : y ∉ S := by
        intro hz
        exact (not_lt_of_ge hlarge) hz.1
      simp only [J, K, Set.indicator_of_notMem hnotS,
        Set.indicator_of_mem hL, zero_sub]
      unfold SpectrallyNegativeLevy.generatorIntegrand
      simp [Set.indicator_of_notMem hnot, hzero]
    · have hy1 : -1 < y := lt_of_not_ge hlarge
      have hS : y ∈ S := ⟨hy1, hy⟩
      have hnotL : y ∉ L := by
        intro hz
        exact (not_lt_of_ge hz.1) hy1
      have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy1, by linarith [hy, hx0]⟩
      simp only [J, K, Set.indicator_of_mem hS,
        Set.indicator_of_notMem hnotL, sub_zero]
      unfold SpectrallyNegativeLevy.generatorIntegrand
      simp only [Set.indicator_of_mem hmem, Pi.one_apply]
      rw [hzero, hder]
      ring
  have heq :
      (∫ y in Iio (-x),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) =
      ∫ y in Iio (-x), J y - K y ∂X.ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    exact hpoint y hy
  have hsubS : S ⊆ Iio (-x) := by
    intro y hy
    exact hy.2
  have hsubL : L ⊆ Iio (-x) := by
    intro y hy
    exact hy.2
  have hJid :
      (∫ y in Iio (-x), J y ∂X.ν) =
      ∫ y in Ioo (-1 : ℝ) (-x), -vcstar W x - y ∂X.ν := by
    dsimp [J]
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [Set.inter_eq_right.mpr hsubS]
  have hKid :
      (∫ y in Iio (-x), K y ∂X.ν) =
      (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x := by
    dsimp [K]
    rw [setIntegral_indicator (measurableSet_Iic.inter measurableSet_Iio)]
    rw [Set.inter_eq_right.mpr hsubL]
    simp only [setIntegral_const]
    ring
  refine ⟨hdom, ?_⟩
  rw [heq]
  rw [integral_sub hj.integrableOn hk.integrableOn]
  rw [hJid, hKid]
