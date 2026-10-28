-- Prove2me | solution 1 for AvramDividend.Classical.ae_negative_near_zero_of_ae_rogozin_negative_slopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:46:38.316719+00:00
-- url     : https://prove2.me/submissions/77633c58-6cb3-49bf-942b-964f2ea43272

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Bornology.Real
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hSlope : ∀ᵐ ω ∂P, ∀ C : ℝ,
      ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
        X.X t ω < C * (t : ℝ)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by
  filter_upwards [hSlope] with ω hω ε hε
  have hf : ∃ᶠ t in 𝓝[>] (0 : ℝ≥0), X.X t ω < (0 : ℝ) := by
    simpa using hω 0
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ≥0), t < ε :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds hε)
  obtain ⟨t, hneg, htε⟩ :=
    (Filter.frequently_iff_forall_eventually_exists_and.mp hf) hb
  exact ⟨t, htε, hneg⟩
