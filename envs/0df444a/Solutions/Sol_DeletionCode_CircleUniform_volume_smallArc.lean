-- Prove2me | solution 1 for DeletionCode.CircleUniform.volume_smallArc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:43:20.034067+00:00
-- url     : https://prove2.me/submissions/63b9dab5-8e9b-498f-ab76-a79ab5bed3df

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform
import Theorems.Thm_DeletionCode_CircleUniform_smallArc_eq_ball

set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal
namespace DeletionCode.CircleUniform
theorem _root_.solution (Q : ℕ) (hQ : 2 ≤ Q) :
    volume (smallArc Q) = ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hQ)
  have htwo : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hsmall : 2 * (1 / (Q : ℝ)) ≤ 1 := by
    calc
      2 * (1 / (Q : ℝ)) = 2 / (Q : ℝ) := by ring
      _ ≤ 1 := (div_le_one hQr).mpr htwo
  have hae : Metric.closedBall (0 : UnitAddCircle) (1 / (Q : ℝ)) =ᵐ[volume]
      Metric.ball (0 : UnitAddCircle) (1 / (Q : ℝ)) :=
    AddCircle.closedBall_ae_eq_ball
  rw [smallArc_eq_ball, ← measure_congr hae, AddCircle.volume_closedBall, min_eq_right hsmall]
  congr 1
  ring
end DeletionCode.CircleUniform
