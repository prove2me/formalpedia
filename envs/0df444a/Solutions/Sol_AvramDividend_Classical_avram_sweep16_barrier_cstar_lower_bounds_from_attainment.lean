-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_barrier_cstar_lower_bounds_from_attainment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:47:38.959559+00:00
-- url     : https://prove2.me/submissions/2ab94e33-0664-4a81-b27e-89bc4c861f2f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital

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
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      ENNReal.ofReal (vcstar W x) ≤ valueFunctionLe X q (cstar W) x ∧
      ENNReal.ofReal (vcstar W x) ≤ valueFunction X q x := by
  intro x hx
  obtain ⟨hD, hValue⟩ :=
    barrier_cstar_attains_value_all_capital X hX q hq W hW hc x hx
  have hcap :
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) ≤
        valueFunctionLe X q (cstar W) x := by
    unfold valueFunctionLe
    exact le_iSup_of_le (barrierStrategy X x (cstar W).toReal)
      (le_iSup_of_le hD (le_refl _))
  have hun :
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) ≤
        valueFunction X q x := by
    unfold valueFunction
    exact le_iSup_of_le (barrierStrategy X x (cstar W).toReal)
      (le_iSup_of_le hD.1 (le_refl _))
  rw [hValue] at hcap hun
  exact ⟨hcap, hun⟩
