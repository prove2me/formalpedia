-- Prove2me | solution 1 for AvramDividend.Classical.levy_path_bddBelow_of_local_boundedness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:22:16.262672+00:00
-- url     : https://prove2.me/submissions/35f8b3a2-5030-4aa1-aecb-b3d989250ad1

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Bornology
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-- A locally bounded Lévy sample trajectory is bounded below on every
finite time horizon. The remaining stochastic step is local boundedness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω)
    (hloc : ∀ s : ℝ≥0, ∃ u ∈ 𝓝 s,
      Bornology.IsBounded ((fun r : ℝ≥0 => X.X r ω) '' u)) :
    BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by
  have hc : IsCompact (Icc (0 : ℝ≥0) t) := isCompact_Icc
  have hb : Bornology.IsBounded
      ((fun r : ℝ≥0 => X.X r ω) '' Icc 0 t) :=
    Bornology.isBounded_image_of_isLocallyBounded_of_isCompact hc hloc
  have heq : ((fun r : ℝ≥0 => X.X r ω) '' Icc 0 t) =
      {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, ⟨by positivity, hs⟩, rfl⟩
  rw [← heq]
  exact hb.bddBelow
