-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_source_nonjump_iff_continuous_at
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:39:14.497873+00:00
-- url     : https://prove2.me/submissions/e9e72dbd-81a7-4043-aa16-800cac91bee9

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- An actual Lévy sample path is continuous at a positive time precisely when
the genuine original-path jump mark there vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    X.X t ω -
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = 0 ↔
      ContinuousAt (fun u : ℝ≥0 => X.X u ω) t := by
  letI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  constructor
  · intro hNoJump
    obtain ⟨l, hl⟩ := X.leftLim ω t ht
    have hleftVal :
        Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = l :=
      leftLim_eq_of_tendsto hl
    have hEq : l = X.X t ω := by
      rw [hleftVal] at hNoJump
      exact (sub_eq_zero.mp hNoJump).symm
    have hcLeft :
        ContinuousWithinAt (fun u : ℝ≥0 => X.X u ω) (Iio t) t := by
      change Tendsto (fun u : ℝ≥0 => X.X u ω) (𝓝[<] t)
        (𝓝 (X.X t ω))
      simpa only [hEq] using hl
    have hcBoth :
        ContinuousWithinAt (fun u : ℝ≥0 => X.X u ω)
          (Iio t ∪ Ici t) t :=
      hcLeft.union (X.rightCont ω t)
    simpa only [Set.Iio_union_Ici, continuousWithinAt_univ] using hcBoth
  · intro hCont
    have hleftVal :
        Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = X.X t ω :=
      leftLim_eq_of_tendsto
        (hCont.tendsto.mono_left nhdsWithin_le_nhds)
    simp only [hleftVal, sub_self]
