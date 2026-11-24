-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.cast_mul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:13:01.227458+00:00
-- url     : https://prove2.me/submissions/90a5bb6c-c976-4b4d-9f79-7677ab156c75

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (a : A) : ((z : ℤ) : A) * a = ((z : ℤ) : ℂ) • a := by
  rw [← zsmul_eq_mul, Int.cast_smul_eq_zsmul]
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
