-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nonnegative_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:57:44.154155+00:00
-- url     : https://prove2.me/submissions/a30f227f-9fa3-4b37-b15f-ac6f4ecb2a0d

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.OrderClosed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

/-!
An almost-everywhere pointwise limit of an a.e. nonnegative real
sequence is nonnegative almost everywhere.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    ∀ᵐ ω ∂P, 0 ≤ Z ω := by
  have hall : ∀ᵐ ω ∂P, ∀ n, 0 ≤ Y n ω := ae_all_iff.mpr hY0
  filter_upwards [hall, hconv] with ω hpos hlim
  have hneg :
      Tendsto (fun n => -(Y n ω)) atTop (𝓝 (-Z ω)) := hlim.neg
  have hnonpos : ∀ᶠ n in atTop, -(Y n ω) ≤ 0 :=
    Filter.Eventually.of_forall (fun n => neg_nonpos.mpr (hpos n))
  exact neg_nonpos.mp (le_of_tendsto hneg hnonpos)
