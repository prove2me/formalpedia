-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_global_continuous_of_zero_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:19:25.808334+00:00
-- url     : https://prove2.me/submissions/3c9be0e6-d41b-4b7b-922b-7e0f46da7a2b

import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A scale function with zero origin is continuous across the whole reserve line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hZero : W 0 = 0) :
    Continuous W := by
  have hleftEq : ∀ x ∈ Iic (0 : ℝ), W x = 0 := by
    intro x hx
    change x ≤ 0 at hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact hW.1 x hlt
    · rw [heq]
      exact hZero
  have hleft : ContinuousOn W (Iic (0 : ℝ)) := by
    have hc : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Iic 0) :=
      continuousOn_const
    exact hc.congr (fun x hx => hleftEq x hx)
  have hright : ContinuousOn W (Ici (0 : ℝ)) := hW.2.2.1
  have hclosed : ContinuousOn W (Iic (0 : ℝ) ∪ Ici 0) :=
    hleft.union_of_isClosed hright isClosed_Iic isClosed_Ici
  have hunion : Iic (0 : ℝ) ∪ Ici 0 = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x 0
  exact continuousOn_univ.mp (by simpa only [hunion] using hclosed)
