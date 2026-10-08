-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_zero_zero_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:10:43.542971+00:00
-- url     : https://prove2.me/submissions/87d85e36-3d63-4d49-8b8f-19e6094c9af0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 := by
  rcases hW with ⟨hnegW, hWnonneg, hWcont, hWmono, hWlap⟩
  have hderiv : ∀ x : ℝ, 0 < x → 0 ≤ deriv W x := by
    intro x hx
    have hwithin : 0 ≤ derivWithin W (Ici 0) x :=
      hWmono.derivWithin_nonneg
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds hx)] at hwithin
    exact hwithin
  have hzeroE : (0 : EReal) ≤ derivZeroPlus W :=
    deriv_global_lower_le_right_liminf W 0 hderiv
  have hW0 : 0 ≤ W 0 := hWnonneg 0 (le_refl 0)
  simp only [barrierValue, lt_self_iff_false, if_false, le_refl, if_true]
  have hscale : scaleDeriv W 0 = derivZeroPlus W := by
    simp [scaleDeriv]
  rw [hscale]
  unfold divE
  split_ifs with htop
  · exact le_rfl
  · exact div_nonneg hW0 (EReal.toReal_nonneg hzeroE)
