-- Prove2me | solution 1 for AvramDividend.Classical.chat03_scale_zero_extension_continuous_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:55:25.053588+00:00
-- url     : https://prove2.me/submissions/adb89201-1015-4b89-a755-4fcb1885ca1f

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.ContinuousOn
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
If W(0) vanishes, its negative-side zero extension and nonnegative-side
continuity glue into full continuity at the zero-reserve boundary.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0) :
    ContinuousAt W 0 := by
  have hleft : ContinuousOn W (Set.Iic (0 : ℝ)) := by
    apply ContinuousOn.congr
      (continuousOn_const :
        ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Iic (0 : ℝ)))
    intro y hy
    by_cases hneg : y < 0
    · exact hW.1 y hneg
    · have hy0 : y = 0 := le_antisymm hy (le_of_not_gt hneg)
      simpa [hy0] using hzero
  have hright : ContinuousOn W (Set.Ici (0 : ℝ)) := hW.2.2.1
  have hall : ContinuousOn W (Set.Iic (0 : ℝ) ∪ Set.Ici 0) :=
    (continuousOn_union_iff_of_isClosed isClosed_Iic isClosed_Ici).2
      ⟨hleft, hright⟩
  have huniv : Set.Iic (0 : ℝ) ∪ Set.Ici 0 = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ,
      iff_true]
    exact le_total y 0
  have hmem : Set.Iic (0 : ℝ) ∪ Set.Ici 0 ∈ 𝓝 (0 : ℝ) := by
    rw [huniv]
    exact Filter.univ_mem
  exact hall.continuousAt hmem
