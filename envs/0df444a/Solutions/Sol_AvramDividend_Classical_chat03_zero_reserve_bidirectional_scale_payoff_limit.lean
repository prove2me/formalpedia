-- Prove2me | solution 1 for AvramDividend.Classical.chat03_zero_reserve_bidirectional_scale_payoff_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:00:42.481987+00:00
-- url     : https://prove2.me/submissions/dc3c8dd1-4147-42f7-8d84-364cdc50f588

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_zero_extension_continuous_at_zero
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
When W(0)=0 and the passage reserve is zero, the discounted scale
payoff converges for all right-approaching sampled times, even if the
sampled reserves straddle zero infinitely often.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (τ : ℝ≥0) (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici τ] τ))
    (discount : ℝ≥0 → ℝ) (hdiscount : ContinuousAt discount τ)
    (hreserveZero : x + X.X τ ω = 0) :
    Tendsto
      (fun n : ℕ => discount (clock n) * W (x + X.X (clock n) ω))
      atTop (𝓝 (discount τ * W (x + X.X τ ω))) := by
  have hWAt : ContinuousAt W (x + X.X τ ω) := by
    rw [hreserveZero]
    exact chat03_scale_zero_extension_continuous_at_zero X q W hW hzero
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
    hWAt.tendsto.comp hreserve
  have hclockAt : Tendsto clock atTop (𝓝 τ) :=
    (tendsto_nhdsWithin_iff.mp hclock).1
  have hdiscountAt : Tendsto (fun n : ℕ => discount (clock n))
      atTop (𝓝 (discount τ)) :=
    hdiscount.tendsto.comp hclockAt
  exact hdiscountAt.mul hscale
