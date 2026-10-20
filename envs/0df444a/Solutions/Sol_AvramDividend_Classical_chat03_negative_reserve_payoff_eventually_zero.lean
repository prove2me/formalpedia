-- Prove2me | solution 1 for AvramDividend.Classical.chat03_negative_reserve_payoff_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:47:11.609979+00:00
-- url     : https://prove2.me/submissions/3e227bdc-111c-48eb-b942-982ffab4da31

import Definitions.Def_AvramDividend_Classical_ScaleFunction
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
At a strictly negative reserve, a right-sided sample-time approximation
eventually stays below zero. The official scale function is zero there,
so any discounted sampled scale payoff eventually vanishes. This remains
valid even if W has a jump at zero.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (τ : ℝ≥0) (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici τ] τ))
    (discount : ℝ≥0 → ℝ)
    (hnegative : x + X.X τ ω < 0) :
    ∀ᶠ n : ℕ in atTop,
      discount (clock n) * W (x + X.X (clock n) ω) = 0 := by
  have hX : Tendsto (fun n : ℕ => X.X (clock n) ω) atTop
      (𝓝 (X.X τ ω)) :=
    (X.rightCont ω τ).tendsto.comp hclock
  have hreserve : Tendsto
      (fun n : ℕ => x + X.X (clock n) ω) atTop
      (𝓝 (x + X.X τ ω)) :=
    tendsto_const_nhds.add hX
  have hneg : ∀ᶠ n : ℕ in atTop,
      x + X.X (clock n) ω < 0 :=
    hreserve.eventually (isOpen_Iio.mem_nhds hnegative)
  filter_upwards [hneg] with n hn
  rw [hW.1 (x + X.X (clock n) ω) hn, mul_zero]
