-- Prove2me | solution 1 for AvramDividend.Classical.chat03_strict_exit_right_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:47:45.216623+00:00
-- url     : https://prove2.me/submissions/20837082-dec8-424d-9b07-967b5622e11f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_two_sided_exit_right_eventually
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Concrete right interval of strict exit, extracted from the already
Proved right-neighbourhood persistence. Its endpoints are nonnegative
real clock times, without any filtration assumptions beyond X.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (lower upper : ℝ)
    (h : X.X t ω < lower ∨ upper < X.X t ω) :
    ∃ u : ℝ≥0, t < u ∧
      ∀ s : ℝ≥0, t ≤ s → s < u →
        X.X s ω < lower ∨ upper < X.X s ω := by
  have hright :=
    chat03_strict_two_sided_exit_right_eventually X ω t lower upper h
  have hnhds : ∀ᶠ s in 𝓝 t,
      s ∈ Set.Ici t →
        X.X s ω < lower ∨ upper < X.X s ω :=
    eventually_nhdsWithin_iff.mp hright
  have hmem :
      {s : ℝ≥0 | s ∈ Set.Ici t →
        X.X s ω < lower ∨ upper < X.X s ω} ∈ 𝓝 t := hnhds
  have htlt : t < t + 1 := lt_add_of_pos_right t zero_lt_one
  obtain ⟨u, hu, hsub⟩ :=
    exists_Ico_subset_of_mem_nhds' hmem htlt
  exact ⟨u, hu.1, fun s hts hsu =>
    (hsub ⟨hts, hsu⟩) hts⟩