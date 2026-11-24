-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.Adapted.mulVec_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:27:04.076807+00:00
-- url     : https://prove2.me/submissions/fa49a4bd-f531-482d-89b5-b7875d7497e5

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.Adapted
open Formalism.REAL
namespace Formalism.FourierDecayAlt.Q.Adapted
theorem _root_.solution {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (k : Fin n) :
    (Q *ᵥ fun p => P p k) = Pi.single k 1 := by
  funext i
  have h1 := congrFun (congrFun h i) k
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simp only [Matrix.mulVec, dotProduct, h1, Pi.single_apply]
end Formalism.FourierDecayAlt.Q.Adapted
