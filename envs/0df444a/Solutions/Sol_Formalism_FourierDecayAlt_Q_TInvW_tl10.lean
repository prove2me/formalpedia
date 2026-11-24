-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.tl10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:06.188138+00:00
-- url     : https://prove2.me/submissions/3ff721b4-b87f-40fa-b6f0-5471bce25b40

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 1 0 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i) f) := rfl
end Formalism.FourierDecayAlt.Q.TInvW
