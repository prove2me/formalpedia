-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:48:06.438567+00:00
-- url     : https://prove2.me/submissions/cde5f77c-4ac8-4658-b3c6-e1f2685bc2c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality

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
    (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hLocal : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  have hInterior :
      ∀ x : ℝ, 0 ≤ x → x ≤ (cstar W).toReal →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
    intro x hx hxc
    have hCap : ENNReal.ofReal x ≤ cstar W := by
      calc
        ENNReal.ofReal x ≤ ENNReal.ofReal (cstar W).toReal :=
          ENNReal.ofReal_le_ofReal hxc
        _ = cstar W := ENNReal.ofReal_toReal (ne_of_lt hc)
    exact hLocal x hx hCap
  intro x hx
  exact le_of_eq
    (avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality
      X hX q hq W hW hc h_smooth hInterior x hx)
