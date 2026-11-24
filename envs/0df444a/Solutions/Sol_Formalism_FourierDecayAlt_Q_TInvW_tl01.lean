-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.tl01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:05.216437+00:00
-- url     : https://prove2.me/submissions/d4427291-20a2-4e11-b260-1555c73af830

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
    tL k r z z' i Y 0 1 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i) f) := rfl
end Formalism.FourierDecayAlt.Q.TInvW
