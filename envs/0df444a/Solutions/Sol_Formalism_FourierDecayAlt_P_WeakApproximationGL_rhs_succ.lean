-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.rhs_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:21.080827+00:00
-- url     : https://prove2.me/submissions/d186cb51-3ab6-4acd-a262-8b09f5b69955

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakApproximationGL
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P.WeakApproximationGL
theorem _root_.solution {m : ℕ} (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1))
    (j : Fin (m + 2)) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) i.succ j =
      (if (j : ℕ) = i then t else 0) + triXY x y i.succ j := by
  simp only [triXY, subShift, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.diagonal_apply, Fin.val_succ, smul_eq_mul, Fin.cons_succ]
  have hiff : ((j : ℕ) + 1 = (i : ℕ) + 1) ↔ ((j : ℕ) = i) := by omega
  by_cases hj : (j : ℕ) = i
  · rw [if_pos (hiff.mpr hj), if_pos hj]
    ring
  · rw [if_neg (fun h => hj (hiff.mp h)), if_neg hj]
    ring
end Formalism.FourierDecayAlt.P.WeakApproximationGL
