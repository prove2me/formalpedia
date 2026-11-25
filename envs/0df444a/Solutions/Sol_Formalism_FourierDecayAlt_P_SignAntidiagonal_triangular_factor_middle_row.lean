-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.triangular_factor_middle_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:02:07.012012+00:00
-- url     : https://prove2.me/submissions/2a9d8973-fe89-4b74-b6fd-3a9fc7410274

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
    (hp : r ≤ p.val ∧ p.val ≤ r + k) : Tn k r j hj y p q = Cf k r j hj y p q := by
  unfold Tn; rw [if_neg (by omega), if_pos hp]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
