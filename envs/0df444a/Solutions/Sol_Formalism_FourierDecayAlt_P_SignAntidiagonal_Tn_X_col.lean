-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.Tn_X_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:33:54.566992+00:00
-- url     : https://prove2.me/submissions/b3ac6fc9-67b8-41f2-8dc4-9de27ebd29a9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hq : q.val < r) : Tn k r j hj y p q = 0 := by
  unfold Tn Cf
  split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.P.SignAntidiagonal
