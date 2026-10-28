-- Prove2me | solution 1 for AvramDividend.Classical.nnreal_rightContinuous_strict_upper_gap_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:16:52.947268+00:00
-- url     : https://prove2.me/submissions/67fee90a-61c8-482b-b1de-1a789af21686

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set Topology
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ) (u : ℝ≥0) (M : ℝ)
    (hRight : ContinuousWithinAt f (Ici u) u)
    (hGap : f u < M) :
    ∃ v : ℝ≥0, u < v ∧
      ∀ t : ℝ≥0, u ≤ t → t < v → f t < M := by
  have hEventually : ∀ᶠ t in 𝓝[≥] u, f t < M :=
    hRight.eventually (Iio_mem_nhds hGap)
  obtain ⟨v, huv, hInterval⟩ :=
    (nhdsGE_basis_Ico u).eventually_iff.mp hEventually
  refine ⟨v, huv, ?_⟩
  intro t hut htv
  exact hInterval ⟨hut, htv⟩
