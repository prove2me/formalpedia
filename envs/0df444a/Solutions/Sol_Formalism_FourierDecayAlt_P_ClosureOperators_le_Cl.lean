-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.le_Cl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:55:20.754124+00:00
-- url     : https://prove2.me/submissions/df04c501-d387-475b-a595-637e526e62f8

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {N : ℕ} (E : Fin N → Fin N → Module.End ℂ V) (L : Fin N → Fin N → Prop) (M : Submodule ℂ V) :
    M ≤ Cl E L M := le_sInf fun _ hP => hP.1
end Formalism.FourierDecayAlt.P.ClosureOperators
