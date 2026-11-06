-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep17_vcstar_nonnegative_without_smoothness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:03:35.001455+00:00
-- url     : https://prove2.me/submissions/cf8a1dd0-3de4-4c63-b2dc-d2e511da6a05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_nonneg
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar

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
    ∀ x : ℝ, 0 ≤ x → 0 ≤ vcstar W x := by
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_finite_cstar X hX q hq W hW hc
  have hzero : 0 ≤ vcstar W 0 := by
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
      have hWzero : 0 ≤ W 0 := hW.2.1 0 le_rfl
      have hdc : 0 ≤ deriv W (cstar W).toReal :=
        scaleDeriv_nonneg X q W hW _ hcrealpos
      unfold vcstar barrierValue
      rw [if_neg (not_lt.mpr (le_refl (0 : ℝ)))]
      rw [if_pos (le_of_lt hcrealpos)]
      simp [scaleDeriv, divE, ne_of_gt hcrealpos]
      exact div_nonneg hWzero hdc
  intro x hx
  exact hzero.trans (hmono hx)
