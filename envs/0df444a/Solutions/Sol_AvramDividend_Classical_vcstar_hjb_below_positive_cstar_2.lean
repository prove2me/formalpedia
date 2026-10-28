-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_hjb_below_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:34:27.934237+00:00
-- url     : https://prove2.me/submissions/f3c22ae8-2a55-4932-ba78-21069834ab40
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_bv_unconditional_20261026

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcfin : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hcpos : 0 < cstar W) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  intro y hy hycap
  have hybar : y < (cstar W).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal
      (le_of_lt hy) (ne_of_lt hcfin)).mp hycap
  have hyint : y ∈ Ioo 0 (cstar W).toReal := ⟨hy, hybar⟩
  by_cases hBV : X.BoundedVariation
  · have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
      scaleFunction_contDiffOn_one_of_boundedVariation
        X hX q hq W hW hBV
    obtain ⟨_, htilt⟩ :=
      scaleFunction_tilted_positive_monotone_of_bv
        X hX q hq W hW hBV
    have hgrad :=
      vcstar_deriv_ge_one_of_scale_C1_tilt
        X hX q hq W hW hC1 htilt
    obtain ⟨hdom, heq⟩ :=
      generator_vcstar_eq_zero_bv_unconditional_20261026
        X hX hBV q hq W hW hcpos y hyint
    have hle : 1 - deriv (vcstar W) y ≤ 0 :=
      sub_nonpos.mpr (hgrad y hy).2
    refine ⟨hdom, ?_⟩
    rw [heq]
    exact max_eq_left hle
  · have hreg : 0 < X.σ ∨ X.BoundedVariation ∨
        ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal) := by
      rcases h_smooth with hσ | hbv | hC2
      · exact Or.inl hσ
      · exact False.elim (hBV hbv)
      · exact Or.inr (Or.inr (hC2.mono (by
          intro z hz
          exact hz.1)))
    obtain ⟨hdom, heq⟩ :=
      generator_vcstar_eq_zero
        X hX q hq W hW hreg hcpos y hyint
    have hle : 1 - deriv (vcstar W) y ≤ 0 :=
      sub_nonpos.mpr
        (vcstar_deriv_ge_one X hX q hq W hW y hy).2
    refine ⟨hdom, ?_⟩
    rw [heq]
    exact max_eq_left hle
