-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep17_vcstar_nonnegative_all_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:47:00.300253+00:00
-- url     : https://prove2.me/submissions/716be687-11d1-4303-a722-ae30bf4f13b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity

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
    (hW : IsScaleFunction X q W) (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ vcstar W x := by
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_finite_cstar X hX q hq W hW hc
  have hzero : 0 ≤ vcstar W 0 :=
    (vcstar_unrestricted_verification_regularity
      X hX q hq W hW hc h_smooth).2.1
  intro x hx
  exact hzero.trans (hmono hx)
