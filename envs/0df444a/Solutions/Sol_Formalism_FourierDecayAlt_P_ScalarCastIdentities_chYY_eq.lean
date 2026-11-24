-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.chYY_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:51.797914+00:00
-- url     : https://prove2.me/submissions/dfa9e9a7-d9c6-4d66-985b-ede71af9e295

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
variable {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution (w : ℂ) (y η : Fin t → A) :
    chYY E w y η = ∑ i, ∑ j, η i * y j * mS E i j w := by
  unfold chYY mS
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm]
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
