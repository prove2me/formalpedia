-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep17_vcstar_positive_cap_interior_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:51:18.911018+00:00
-- url     : https://prove2.me/submissions/df609063-c7c9-4fea-8b5a-1530a42f374b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hsmooth_inner :
      0 < X.σ ∨ X.BoundedVariation ∨
        ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal) := by
    rcases h_smooth with hσ | hBV | hC2
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hBV)
    · exact Or.inr (Or.inr (hC2.mono (by
        intro z hz
        exact hz.1)))
  intro y hy hyl
  have hylt : y < (cstar W).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hctop).mp hyl
  have hgen :=
    generator_vcstar_eq_zero
      X hX q hq W hW hsmooth_inner hcpos y ⟨hy, hylt⟩
  have hder := vcstar_deriv_ge_one X hX q hq W hW y hy
  refine ⟨hgen.1, ?_⟩
  rw [hgen.2]
  exact max_eq_left (sub_nonpos.mpr hder.2)
