-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:11:38.44591+00:00
-- url     : https://prove2.me/submissions/966f7586-c1e6-4825-9547-356123e0b5d0

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A nonlinear left-jump of the literal controlled reserve is exactly the
nonlinear original-source jump from the true prepayment left reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let J : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    w (riskProcess X x D t ω) -
      w (Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t) =
    w (Y + J) - w Y := by
  dsimp only
  let Y : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let J : ℝ :=
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
  have hleft :
      Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t = Y :=
    avram_wave4_p2_original_prepost_reserve_same_leftlim
      X x D hD ω t ht
  have hmark :
      riskProcess X x D t ω -
        Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t = J :=
    avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
      X x D hD ω t ht
  have hvalue : riskProcess X x D t ω = Y + J := by
    rw [hleft] at hmark
    linarith
  rw [hleft, hvalue]
