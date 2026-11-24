-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.arg_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:01.254601+00:00
-- url     : https://prove2.me/submissions/eb881d91-f955-4eb4-a305-1a428a7338e6

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DegreeMapArithmetic
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.DegreeMapArithmetic
theorem _root_.solution {t : ℕ} (w : ℂ) (j : Fin t) :
    w - (t : ℂ) + 1 + (((Fin.rev j : Fin t) : ℕ) : ℂ) = w - ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [Fin.val_rev, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ t)]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
