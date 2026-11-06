-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_capped_boundary_bound_extends_above_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:21:31.045179+00:00
-- url     : https://prove2.me/submissions/81d4ee86-00b7-40ca-aa20-da8b7c44a80a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q c : ℝ) (hc : 0 ≤ c)
    (w : ℝ → ℝ) (hwc : 0 ≤ w c)
    (hBoundary : valueFunctionLe X q (ENNReal.ofReal c) c ≤ ENNReal.ofReal (w c))
    (hAffine : ∀ x : ℝ, c < x → w x = x - c + w c) :
    ∀ x : ℝ, c ≤ x →
      valueFunctionLe X q (ENNReal.ofReal c) x ≤ ENNReal.ofReal (w x) := by
  intro x hcx
  rcases eq_or_lt_of_le hcx with heq | hgt
  · subst x
    exact hBoundary
  · have hdiff : 0 ≤ x - c := sub_nonneg.mpr (le_of_lt hgt)
    calc
      valueFunctionLe X q (ENNReal.ofReal c) x =
          ENNReal.ofReal (x - c) +
            valueFunctionLe X q (ENNReal.ofReal c) c :=
        valueFunctionLe_above_cap X q x c hc hgt
      _ ≤ ENNReal.ofReal (x - c) + ENNReal.ofReal (w c) :=
        add_le_add (le_refl _) hBoundary
      _ = ENNReal.ofReal (w x) := by
        rw [← ENNReal.ofReal_add hdiff hwc, hAffine x hgt]
