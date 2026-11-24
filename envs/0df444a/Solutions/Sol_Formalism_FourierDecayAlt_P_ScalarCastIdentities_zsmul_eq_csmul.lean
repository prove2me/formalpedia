-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.zsmul_eq_csmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:54.674853+00:00
-- url     : https://prove2.me/submissions/47179331-a53f-40f0-b647-0f2dff892385

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (a : A) : z • a = ((z : ℤ) : ℂ) • a := by
  rw [Int.cast_smul_eq_zsmul]
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
