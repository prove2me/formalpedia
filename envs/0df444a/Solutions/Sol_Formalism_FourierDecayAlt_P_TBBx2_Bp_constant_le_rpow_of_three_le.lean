-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Bp.constant_le_rpow_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:25.402507+00:00
-- url     : https://prove2.me/submissions/b97e28f0-d074-432c-b30b-c154325b533c

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Bp
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P.TBBx2.Bp
theorem _root_.solution (C₂ b : ℝ) (hC₂ : 0 < C₂) (hb : 3 ≤ b) : C₂ ≤ b ^ (max 0 (Real.log C₂ / Real.log 3)) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rcases le_total (Real.log C₂ / Real.log 3) 0 with h | h
  · rw [max_eq_left h, Real.rpow_zero]
    have hl : Real.log C₂ ≤ 0 := by
      have := (div_le_iff₀ h3).mp h
      linarith
    calc C₂ = Real.exp (Real.log C₂) := (Real.exp_log hC₂).symm
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hl
      _ = 1 := Real.exp_zero
  · rw [max_eq_right h]
    have h3' : Real.log 3 ≠ 0 := h3.ne'
    have e3 : (3 : ℝ) ^ (Real.log C₂ / Real.log 3) = C₂ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      rw [show Real.log 3 * (Real.log C₂ / Real.log 3) = Real.log C₂ by field_simp]
      exact Real.exp_log hC₂
    calc C₂ = (3 : ℝ) ^ (Real.log C₂ / Real.log 3) := e3.symm
      _ ≤ b ^ (Real.log C₂ / Real.log 3) := Real.rpow_le_rpow (by norm_num) hb h
end Formalism.FourierDecayAlt.P.TBBx2.Bp
