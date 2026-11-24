-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.rhoOf_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:06.575324+00:00
-- url     : https://prove2.me/submissions/b57a1e56-3c61-4bac-8fcd-9d5d8c7f2782

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_prj_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ)
    (hΓ : IsUnit (Vᴴ * H * V).det) (m : ℕ) :
    (rhoOf H V Φ - 1) ^ (m + 1) = V * (Φ - 1) ^ (m + 1) * prj H V := by
  have hW : rhoOf H V Φ - 1 = V * (Φ - 1) * prj H V := by
    simp only [rhoOf, add_sub_cancel_left]
  have hP := prj_mul H V hΓ
  induction m with
  | zero => rw [zero_add, pow_one, pow_one, hW]
  | succ k ih =>
    rw [pow_succ (rhoOf H V Φ - 1) (k + 1), ih, hW]
    calc V * (Φ - 1) ^ (k + 1) * prj H V * (V * (Φ - 1) * prj H V)
        = V * (Φ - 1) ^ (k + 1) * (prj H V * V) * (Φ - 1) * prj H V := by
          simp only [Matrix.mul_assoc]
      _ = V * (Φ - 1) ^ (k + 1 + 1) * prj H V := by
          rw [hP, Matrix.mul_one, pow_succ (Φ - 1) (k + 1), Matrix.mul_assoc V ((Φ - 1) ^ (k + 1)) (Φ - 1)]
end Formalism.FourierDecayAlt.P.HermitianProjections
