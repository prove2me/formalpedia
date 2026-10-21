-- Prove2me | solution 1 for AvramDividend.Classical.chat03_strict_lower_exit_right_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:27:36.737601+00:00
-- url     : https://prove2.me/submissions/c2e8dad2-cf65-4a96-91dd-61f8e802c8e1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
A strict downward crossing persists throughout an explicit nonempty
right-hand interval of every right-continuous Lévy sample path.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (lower : ℝ)
    (h : X.X t ω < lower) :
    ∃ u : ℝ≥0, t < u ∧
      ∀ s : ℝ≥0, t ≤ s → s < u → X.X s ω < lower := by
  have hright : ∀ᶠ s in 𝓝[Set.Ici t] t,
      X.X s ω < lower :=
    (X.rightCont ω t).eventually (isOpen_Iio.mem_nhds h)
  have hnhds : ∀ᶠ s in 𝓝 t,
      s ∈ Set.Ici t → X.X s ω < lower :=
    eventually_nhdsWithin_iff.mp hright
  have hmem :
      {s : ℝ≥0 | s ∈ Set.Ici t → X.X s ω < lower} ∈ 𝓝 t := hnhds
  obtain ⟨u, hu, hsub⟩ :=
    exists_Ico_subset_of_mem_nhds' hmem
      (lt_add_of_pos_right t zero_lt_one)
  exact ⟨u, hu.1, fun s hts hsu => (hsub ⟨hts, hsu⟩) hts⟩
