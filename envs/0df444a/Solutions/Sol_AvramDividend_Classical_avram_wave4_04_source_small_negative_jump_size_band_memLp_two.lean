-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_source_small_negative_jump_size_band_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:55:23.891715+00:00
-- url     : https://prove2.me/submissions/72948273-a6f9-4af2-9b1a-cadd7bca963c

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open AvramDividend.Classical

/-- A source Lévy measure gives an L² intensity for the positive sizes of
small negative jumps on any finite time band. This remains an intensity
statement; it does not assert a random-measure compensation identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ) :
    MemLp ((Set.Ioc s t ×ˢ Set.Ioo (0 : ℝ) 1).indicator
      (fun p : ℝ × ℝ => p.2)) 2
      (volume.prod (X.ν.map (fun y : ℝ => -y))) := by
  have hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    calc
      (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) ≤
          (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) := by
        simpa using (lintegral_mono_set
          (Set.subset_univ (Iio (0 : ℝ))) :
          (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) ≤
            ∫⁻ y in Set.univ, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν)
      _ < ⊤ := X.ν_integrable
  let ν := X.ν.map (fun y : ℝ => -y)
  letI : SigmaFinite ν :=
    gaussian_negative_jump_pushforward_sigmaFinite X.ν X.ν_Ici hlevy
  have hν2 : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) < ⊤ :=
    gaussian_levy_square_integrable_neg_pushforward X.ν hlevy
  have hsmall_sq : (∫⁻ z in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (z ^ 2) ∂ν) < ⊤ := by
    calc
      (∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (z ^ 2) ∂ν) =
          ∫⁻ z in Ioi (0 : ℝ), (Ioo (0 : ℝ) 1).indicator
            (fun z : ℝ => ENNReal.ofReal (z ^ 2)) z ∂ν := by
        rw [lintegral_indicator measurableSet_Ioo]
        have hs : Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo 0 1 :=
          Set.inter_eq_left.mpr (fun z hz => hz.1)
        simp [hs]
      _ ≤ (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ Ioo (0 : ℝ) 1
        · simp only [Set.indicator_of_mem hz]
          have hz2 : z ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
          simp [min_eq_right hz2]
        · simp [Set.indicator_of_notMem hz]
      _ < ⊤ := hν2
  have hintegrable : Integrable (fun z : ℝ => z ^ 2)
      (ν.restrict (Ioo (0 : ℝ) 1)) := by
    refine ⟨(by fun_prop), ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun z : ℝ => sq_nonneg z))]
    exact hsmall_sq
  have hsize : MemLp (fun z : ℝ => z) 2
      (ν.restrict (Ioo (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hintegrable
  have hprod : MemLp (fun p : ℝ × ℝ => p.2) 2
      ((volume.restrict (Ioc s t)).prod (ν.restrict (Ioo (0 : ℝ) 1))) :=
    hsize.comp_snd (volume.restrict (Ioc s t))
  apply (memLp_indicator_iff_restrict
    (measurableSet_Ioc.prod measurableSet_Ioo)).2
  rw [← Measure.prod_restrict]
  exact hprod
