-- Prove2me | solution 1 for AvramDividend.Classical.path_value_le_of_strict_prefix_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:33:26.138359+00:00
-- url     : https://prove2.me/submissions/970d9d5c-7805-47cc-8fb7-b74f47984f43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hpre : ∀ t : ℝ≥0, t < u → X.X t ω ≤ b) :
    X.X u ω ≤ b := by
  by_cases huz : u = 0
  · subst u
    simpa [X.X_zero ω] using hb
  · have hu : 0 < u := lt_of_le_of_ne
        (zero_le : (0 : ℝ≥0) ≤ u) (Ne.symm huz)
    letI : (𝓝[<] u).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
    obtain ⟨l, hl⟩ := X.leftLim ω u hu
    have hev : ∀ᶠ t in 𝓝[<] u, X.X t ω ∈ Set.Iic b := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hpre t (Set.mem_Iio.mp ht)
    have hle : l ≤ b :=
      isClosed_Iic.mem_of_tendsto hl hev
    exact (X.noPosJumps ω u l hu hl).trans hle
