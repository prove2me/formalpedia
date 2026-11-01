-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_hjb_from_source_scale_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:36:40.846004+00:00
-- url     : https://prove2.me/submissions/03eacb76-f613-45ca-8444-d8db160a3f7e

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_hjb_of_interior_scale
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Complete Gaussian positive-axis HJB assembled from genuine source scale harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hscale : ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  by_cases hc0 : cstar W = 0
  · exact vcstar_hjb_all_positive_of_generator_zero_barrier X q W hc0 hgen
  have hfin := cstar_lt_top X hX q hq W hW
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos hc0 (ne_of_lt hfin)
  have hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 := by
    intro x hx
    exact (hscale x hx.1).2
  have hvcstar := vcstar_interior_harmonicity_of_scale_harmonicity
    X q W hW ha (by
      intro x hx
      exact hscale x hx.1)
  intro y hy
  rcases lt_trichotomy y (cstar W).toReal with hlt | heq | hgt
  · have hyin : y ∈ Ioo 0 (cstar W).toReal := ⟨hy, hlt⟩
    have hval := hvcstar y hyin
    have hder := (vcstar_deriv_ge_one X hX q hq W hW y hy).2
    refine ⟨hval.1, ?_⟩
    rw [hval.2]
    exact max_eq_left (sub_nonpos.mpr hder)
  · subst y
    have he := avram_ws01e_bf_new_gaussian_cstar_hjb_of_interior_scale
      X hX q hq W hW hσ ha hinside
    exact ⟨he.1, he.2.2⟩
  · exact (vcstar_hjb_above_cstar_of_generator X q W hgen) y hgt
