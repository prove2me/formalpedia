-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep17_vcstar_finite_barrier_boundary_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:02:55.113782+00:00
-- url     : https://prove2.me/submissions/e291d7a0-6b98-4139-a0e6-24a15cc7fb6a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    0 ≤ vcstar W (cstar W).toReal := by
  by_cases hc0 : cstar W = 0
  · have hz := (barrier_zero_boundary_value_nonneg
        X hX q hq W hW).1
    simpa [vcstar, hc0] using hz
  · have hcpos : 0 < cstar W := by
      have hz : (0 : ℝ≥0∞) ≤ cstar W := bot_le
      exact lt_of_le_of_ne hz (Ne.symm hc0)
    have hctop : cstar W ≠ ⊤ := ne_of_lt hc
    have hcrealpos : 0 < (cstar W).toReal :=
      ENNReal.toReal_pos (ne_of_gt hcpos) hctop
    have hcreal0 : 0 ≤ (cstar W).toReal := le_of_lt hcrealpos
    have hWc : 0 ≤ W (cstar W).toReal :=
      hW.2.1 _ hcreal0
    have hdc : 0 ≤ deriv W (cstar W).toReal :=
      scaleDeriv_nonneg X q W hW _ hcrealpos
    simp only [vcstar, barrierValue, not_lt.mpr hcreal0,
      if_false, le_rfl, if_true]
    simp [scaleDeriv, divE, ne_of_gt hcrealpos]
    exact div_nonneg hWc hdc
