-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_chronological_ito_jump_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:22:21.913987+00:00
-- url     : https://prove2.me/submissions/c9d043ab-639e-47fa-a8b2-d5122689869e

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Separate the genuine Lévy jump from the subsequent right-dividend atom.
The correction has the sign required by the source verification jump premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hjump : rightLimit D t ω - D t ω ≤
      w (x + X.X t ω - D t ω) -
        w (x + X.X t ω - rightLimit D t ω)) :
    let before : ℝ :=
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω
    let afterSource : ℝ := x + X.X t ω - D t ω
    let afterPayment : ℝ := x + X.X t ω - rightLimit D t ω
    let sourceJump : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let paymentAtom : ℝ := rightLimit D t ω - D t ω
    (w afterPayment - w before -
        deriv w before * (sourceJump - paymentAtom) =
      (w afterSource - w before - deriv w before * sourceJump) +
        (w afterPayment - w afterSource + deriv w before * paymentAtom)) ∧
      w afterPayment - w afterSource + paymentAtom ≤ 0 := by
  dsimp only
  constructor
  · ring
  · linarith [hjump]
