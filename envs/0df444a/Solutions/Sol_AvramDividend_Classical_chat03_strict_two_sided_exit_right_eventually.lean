-- Prove2me | solution 1 for AvramDividend.Classical.chat03_strict_two_sided_exit_right_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:22:52.372732+00:00
-- url     : https://prove2.me/submissions/4b706890-a047-4abd-b2a3-8f6fcf8bd2ed

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Pure right-continuity bridge for strict two-sided crossing, with no
filtration regularity assumption. An actual strict exit persists locally
to the right, enabling dense dyadic grid approximation of the open event.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (lower upper : ℝ)
    (h : X.X t ω < lower ∨ upper < X.X t ω) :
    ∀ᶠ s in 𝓝[Set.Ici t] t,
      X.X s ω < lower ∨ upper < X.X s ω := by
  have hOpen : IsOpen (Set.Iio lower ∪ Set.Ioi upper) :=
    isOpen_Iio.union isOpen_Ioi
  have hm : X.X t ω ∈ Set.Iio lower ∪ Set.Ioi upper := by
    simpa only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] using h
  have hevent := (X.rightCont ω t).eventually (hOpen.mem_nhds hm)
  filter_upwards [hevent] with s hs
  change X.X s ω ∈ Set.Iio lower ∪ Set.Ioi upper at hs
  simpa only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] using hs
