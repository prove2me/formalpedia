-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_signed_generator_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:19:27.693793+00:00
-- url     : https://prove2.me/submissions/ad6c6608-849a-4051-809d-f95f60d22054

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_jump_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integrable_of_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Source compensated-generator residual bound retaining the exact negative
large-ruin killing mass. The strict zero crossing is deliberate: a jump
landing precisely at reserve zero need not kill a BV scale value. -/
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
          max 0 (-vcstar W x - y) ∂X.ν) -
        (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x -
        q * vcstar W x := by
  let S : Set ℝ := Ioo (-1 : ℝ) (-x)
  let L : Set ℝ := Iic (-1 : ℝ) ∩ Iio (-x)
  let J : ℝ → ℝ := S.indicator
    (fun y : ℝ => max 0 (-vcstar W x - y))
  let K : ℝ → ℝ := L.indicator (fun _ : ℝ => vcstar W x)
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  have hdom := vcstar_generatorIntegrable_strictly_above_real_cstar
    X q W hW x hx
  have hint : IntegrableOn
      (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y)
      (Iio (0 : ℝ)) X.ν := by
    exact hdom
  have hj : Integrable J X.ν :=
    avram_wave4_05_source_ruin_overshoot_integrable_of_levy X W x hx0
  have hLsub : L ⊆ Iic (-x) := by
    intro y hy
    have hylt : y < -x := hy.2
    exact le_of_lt hylt
  have hLfin : X.ν L < ⊤ :=
    lt_of_le_of_lt (measure_mono hLsub)
      (levy_negative_mass_away_from_zero_finite X x hx0)
  have hLconst : IntegrableOn (fun _ : ℝ => vcstar W x) L X.ν := by
    refine IntegrableOn.of_bound hLfin (by fun_prop) |vcstar W x| ?_
    exact Filter.Eventually.of_forall (fun y => by
      simp [Real.norm_eq_abs])
  have hk : Integrable K X.ν :=
    (integrable_indicator_iff (measurableSet_Iic.inter measurableSet_Iio)).mpr hLconst
  have hbound :
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) ≤
        ∫ y in Iio (0 : ℝ), J y - K y ∂X.ν := by
    apply setIntegral_mono_on hint (hj.sub hk).integrableOn measurableSet_Iio
    intro y hy
    have hsigned := avram_wave4_05_source_signed_jump_bound
      X hX q hq W hW x hx y hy
    by_cases hs : y ∈ S
    · by_cases hl : y ∈ L
      · simpa [S, L, J, K, hs, hl] using hsigned
      · simpa [S, L, J, K, hs, hl] using hsigned
    · by_cases hl : y ∈ L
      · simpa [S, L, J, K, hs, hl] using hsigned
      · simpa [S, L, J, K, hs, hl] using hsigned
  have hsubS : S ⊆ Iio (0 : ℝ) := by
    intro y hy
    exact lt_trans hy.2 (neg_lt_zero.mpr hx0)
  have hsubL : L ⊆ Iio (0 : ℝ) := by
    intro y hy
    exact lt_of_le_of_lt hy.1 (by norm_num : (-1 : ℝ) < 0)
  have hJid :
      (∫ y in Iio (0 : ℝ), J y ∂X.ν) =
      ∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν := by
    dsimp [J]
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [Set.inter_eq_right.mpr hsubS]
  have hKid :
      (∫ y in Iio (0 : ℝ), K y ∂X.ν) =
      (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-x)) * vcstar W x := by
    dsimp [K]
    rw [setIntegral_indicator (measurableSet_Iic.inter measurableSet_Iio)]
    rw [Set.inter_eq_right.mpr hsubL]
    simp only [setIntegral_const]
    ring
  refine ⟨hdom, ?_⟩
  rw [vcstar_generator_above_eq_drift_add_jump X W x hx]
  rw [integral_sub hj.integrableOn hk.integrableOn] at hbound
  rw [hJid, hKid] at hbound
  linarith
