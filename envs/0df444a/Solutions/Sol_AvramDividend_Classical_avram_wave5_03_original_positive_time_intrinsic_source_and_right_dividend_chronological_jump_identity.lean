-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_positive_time_intrinsic_source_and_right_dividend_chronological_jump_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T16:02:31.438616+00:00
-- url     : https://prove2.me/submissions/f8a0129d-0854-453b-a0fb-afe629f2091f

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Merge the true Lévy prepayment jump with the subsequent right dividend atom. -/
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
    let A : ℝ := rightLimit D t ω - D t ω
    (w (riskProcess X x D t ω) -
      w (Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t)) +
      (w (riskProcess X x D t ω - A) - w (riskProcess X x D t ω)) =
      w (Y + J - A) - w Y := by
  dsimp only
  let Y : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let J : ℝ :=
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
  let A : ℝ := rightLimit D t ω - D t ω
  have hleft :
      Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t = Y :=
    avram_wave4_p2_original_prepost_reserve_same_leftlim
      X x D hD ω t ht
  have hmark :
      riskProcess X x D t ω -
        Function.leftLim
          (fun s : ℝ≥0 => riskProcess X x D s ω) t = J :=
    avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
      X x D hD ω t ht
  have hvalue : riskProcess X x D t ω = Y + J := by
    rw [hleft] at hmark
    linarith
  have hsource :
      w (riskProcess X x D t ω) -
        w (Function.leftLim
          (fun s : ℝ≥0 => riskProcess X x D s ω) t) =
      w (Y + J) - w Y :=
    avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
      X x D hD w ω t ht
  calc
    (w (riskProcess X x D t ω) -
      w (Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t)) +
      (w (riskProcess X x D t ω - A) - w (riskProcess X x D t ω)) =
        (w (Y + J) - w Y) +
          (w (riskProcess X x D t ω - A) -
            w (riskProcess X x D t ω)) := by rw [hsource]
    _ = w (Y + J - A) - w Y := by rw [hvalue]; ring
