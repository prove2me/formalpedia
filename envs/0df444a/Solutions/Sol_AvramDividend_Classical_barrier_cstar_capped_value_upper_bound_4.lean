-- Prove2me | solution 4 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:38:11.116239+00:00
-- url     : https://prove2.me/submissions/94982fe9-9ee7-4641-8668-4b00a02ca66f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Split the capped verification parent into its zero- and positive-barrier cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ cstar W) with hz | hp
  · have hc0 : cstar W = 0 := hz.symm
    obtain ⟨hnonneg, hvalue0⟩ :=
      zero_cap_boundary_value_package X hX q hq W hW
    intro x hx
    have hbound :=
      zero_cap_value_upper_bound_of_zero_bound X q W hvalue0 hnonneg x hx
    have hvc : vcstar W x = barrierValue W 0 x := by
      change barrierValue W (cstar W).toReal x = barrierValue W 0 x
      simp [hc0]
    simpa only [hc0, hvc] using hbound
  · exact
      barrier_cstar_capped_value_upper_bound_of_positive_cstar
        X hX q hq W hW hc hp h_smooth
