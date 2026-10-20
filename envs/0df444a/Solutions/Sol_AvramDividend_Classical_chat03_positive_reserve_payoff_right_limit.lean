-- Prove2me | solution 1 for AvramDividend.Classical.chat03_positive_reserve_payoff_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:45:20.182239+00:00
-- url     : https://prove2.me/submissions/0ad00393-2112-48e3-80a0-67ad947f55c0

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
For a strictly positive reserve at a continuous-time passage, right-sided
convergence of grid stop times gives convergence of the discounted scale
payoff. The bounded-variation discontinuity of W at zero is excluded by
the explicit positivity condition.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (τ : ℝ≥0) (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici τ] τ))
    (discount : ℝ≥0 → ℝ) (hdiscount : ContinuousAt discount τ)
    (hpositive : 0 < x + X.X τ ω) :
    Tendsto
      (fun n : ℕ => discount (clock n) * W (x + X.X (clock n) ω))
      atTop (𝓝 (discount τ * W (x + X.X τ ω))) := by
  have hwithin : Set.Ici (0 : ℝ) ∈ 𝓝 (x + X.X τ ω) := by
    apply Filter.mem_of_superset (isOpen_Ioi.mem_nhds hpositive)
    intro y hy
    exact (show (0 : ℝ) < y from hy).le
  have hWcont : ContinuousAt W (x + X.X τ ω) :=
    hW.2.2.1.continuousAt hwithin
  have hX : Tendsto (fun n : ℕ => X.X (clock n) ω) atTop
      (𝓝 (X.X τ ω)) :=
    (X.rightCont ω τ).tendsto.comp hclock
  have hreserve : Tendsto
      (fun n : ℕ => x + X.X (clock n) ω) atTop
      (𝓝 (x + X.X τ ω)) :=
    tendsto_const_nhds.add hX
  have hscale : Tendsto
      (fun n : ℕ => W (x + X.X (clock n) ω)) atTop
      (𝓝 (W (x + X.X τ ω))) :=
    hWcont.tendsto.comp hreserve
  have hclockAt : Tendsto clock atTop (𝓝 τ) :=
    (tendsto_nhdsWithin_iff.mp hclock).1
  have hdiscountAt : Tendsto (fun n : ℕ => discount (clock n))
      atTop (𝓝 (discount τ)) :=
    hdiscount.tendsto.comp hclockAt
  exact hdiscountAt.mul hscale
