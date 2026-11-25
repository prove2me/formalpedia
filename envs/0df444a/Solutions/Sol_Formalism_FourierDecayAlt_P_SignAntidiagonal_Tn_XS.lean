-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.Tn_XS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:55:12.735835+00:00
-- url     : https://prove2.me/submissions/2ae682fa-469e-4f8f-94f0-817c59266506

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
    (hp : p.val < r) (hq : r + k < q.val) :
    Tn k r j hj y p q = (if h : 2 * r + k - q.val < j then Zv k r j hj y ⟨2 * r + k - q.val, h⟩ p
        else if h' : p.val < j then -star (Zv k r j hj y ⟨p.val, h'⟩ (tau k r q)) else 0) := by
  unfold Tn; rw [if_pos hp, if_neg (by omega), if_pos hq]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
