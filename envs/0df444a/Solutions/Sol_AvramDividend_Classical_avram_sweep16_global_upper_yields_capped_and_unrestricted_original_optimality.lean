-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_global_upper_yields_capped_and_unrestricted_original_optimality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:19:44.183126+00:00
-- url     : https://prove2.me/submissions/491f7d91-2153-4cbe-8157-4233a28b181a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

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
    (hUpper : ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) ∧
      valueFunction X q x = ENNReal.ofReal (vcstar W x) := by
  intro x hx
  have hCapLe :
      valueFunctionLe X q (cstar W) x ≤ valueFunction X q x := by
    unfold valueFunctionLe valueFunction
    apply iSup_le
    intro D
    apply iSup_le
    intro hD
    exact le_iSup_of_le D (le_iSup_of_le hD.1 (le_refl _))
  have hLower :=
    avram_sweep16_barrier_cstar_lower_bounds_from_attainment
      X hX q hq W hW hc x hx
  exact ⟨le_antisymm (le_trans hCapLe (hUpper x hx)) hLower.1,
    le_antisymm (hUpper x hx) hLower.2⟩
