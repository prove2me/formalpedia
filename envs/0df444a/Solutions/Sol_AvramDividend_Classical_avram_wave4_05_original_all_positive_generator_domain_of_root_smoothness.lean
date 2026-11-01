-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_original_all_positive_generator_domain_of_root_smoothness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:58:24.893666+00:00
-- url     : https://prove2.me/submissions/4b5a1d27-a8a8-4419-bbff-e3f16f492a19

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_vcstar_interior_generator_domain_all_smooth_branches
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_integrable_at_positive_cstar_of_smooth
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The root smoothness alternative puts vcstar in the actual source generator domain everywhere positive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ y : ℝ, 0 < y → X.GeneratorIntegrable (vcstar W) y := by
  have hcfin := cstar_lt_top X hX q hq W hW
  have hlocal : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal) := by
    rcases h_smooth with hσ | hbv | hc2
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hbv)
    · exact Or.inr (Or.inr (hc2.mono (by intro z hz; exact hz.1)))
  have hcap_pos (hr : (0 : ℝ) < (cstar W).toReal) : 0 < cstar W := by
    by_contra hn
    have hzero : cstar W = 0 :=
      le_antisymm (le_of_not_gt hn) zero_le
    simp [hzero] at hr
  intro y hy
  rcases lt_trichotomy y (cstar W).toReal with hbelow | heq | habove
  · have hcpos := hcap_pos (lt_trans hy hbelow)
    exact avram_wave4_05_original_vcstar_interior_generator_domain_all_smooth_branches
      X hX q hq W hW hlocal hcpos y (mem_Ioo.mpr ⟨hy, hbelow⟩)
  · subst y
    have hcpos := hcap_pos hy
    exact avram_wave4_p3_vcstar_generator_integrable_at_positive_cstar_of_smooth
      X hX q hq W hW hcfin hcpos h_smooth
  · exact vcstar_generatorIntegrable_strictly_above_real_cstar
      X q W hW y habove
