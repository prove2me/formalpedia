-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.sum_single_single_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:14.746386+00:00
-- url     : https://prove2.me/submissions/9fe2e124-25d9-4d42-b79d-4f95586285dc

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_single_sum

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
theorem _root_.solution (q p : Fin t) (F : Fin t → Fin t → A) :
    ∑ q', ∑ p', ((Pi.single q (1 : ℂ) : Fin t → ℂ) q' * (Pi.single p (1 : ℂ) : Fin t → ℂ) p') • F q' p' = F q p := by
  simp_rw [mul_smul, ← Finset.smul_sum, single_sum]
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
