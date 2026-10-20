-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nonnegative_reserve_payoff_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:49:18.934008+00:00
-- url     : https://prove2.me/submissions/0c0484b6-1ad0-4de8-9f4f-41501bafa8ee

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
At a nonnegative limiting reserve, right-sampled discounted q-scale
payoffs converge if sampled reserves are eventually nonnegative.
This includes a zero limiting reserve and permits W(0)>0.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (τ : ℝ≥0) (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici τ] τ))
    (discount : ℝ≥0 → ℝ) (hdiscount : ContinuousAt discount τ)
    (hlimit : 0 ≤ x + X.X τ ω)
    (hsampled : ∀ᶠ n : ℕ in atTop, 0 ≤ x + X.X (clock n) ω) :
    Tendsto
      (fun n : ℕ => discount (clock n) * W (x + X.X (clock n) ω))
      atTop (𝓝 (discount τ * W (x + X.X τ ω))) := by
  have hX : Tendsto (fun n : ℕ => X.X (clock n) ω) atTop
      (𝓝 (X.X τ ω)) :=
    (X.rightCont ω τ).tendsto.comp hclock
  have hreserve : Tendsto
      (fun n : ℕ => x + X.X (clock n) ω) atTop
      (𝓝 (x + X.X τ ω)) :=
    tendsto_const_nhds.add hX
  have hwithin : Tendsto
      (fun n : ℕ => x + X.X (clock n) ω) atTop
      (𝓝[Set.Ici (0 : ℝ)] (x + X.X τ ω)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hreserve, hsampled⟩
  have hWcont : ContinuousWithinAt W (Set.Ici (0 : ℝ))
      (x + X.X τ ω) :=
    hW.2.2.1.continuousWithinAt hlimit
  have hscale : Tendsto
      (fun n : ℕ => W (x + X.X (clock n) ω)) atTop
      (𝓝 (W (x + X.X τ ω))) :=
    hWcont.tendsto.comp hwithin
  have hclockAt : Tendsto clock atTop (𝓝 τ) :=
    (tendsto_nhdsWithin_iff.mp hclock).1
  have hdiscountAt : Tendsto (fun n : ℕ => discount (clock n))
      atTop (𝓝 (discount τ)) :=
    hdiscount.tendsto.comp hclockAt
  exact hdiscountAt.mul hscale
