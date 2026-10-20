-- Prove2me | solution 1 for AvramDividend.Classical.chat03_strict_upper_exit_right_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:33:30.069908+00:00
-- url     : https://prove2.me/submissions/3a32f17c-9ac5-4b1f-aaf9-ca383f8769ef

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Right-continuous sample paths preserve an upper strict crossing
over an explicit nonempty right interval.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (upper : ℝ)
    (h : upper < X.X t ω) :
    ∃ u : ℝ≥0, t < u ∧
      ∀ s : ℝ≥0, t ≤ s → s < u → upper < X.X s ω := by
  have hright : ∀ᶠ s in 𝓝[Set.Ici t] t,
      upper < X.X s ω :=
    (X.rightCont ω t).eventually (isOpen_Ioi.mem_nhds h)
  have hnhds : ∀ᶠ s in 𝓝 t,
      s ∈ Set.Ici t → upper < X.X s ω :=
    eventually_nhdsWithin_iff.mp hright
  have hmem :
      {s : ℝ≥0 | s ∈ Set.Ici t → upper < X.X s ω} ∈ 𝓝 t := hnhds
  obtain ⟨u, hu, hsub⟩ :=
    exists_Ico_subset_of_mem_nhds' hmem
      (lt_add_of_pos_right t zero_lt_one)
  exact ⟨u, hu.1, fun s hts hsu => (hsub ⟨hts, hsu⟩) hts⟩
