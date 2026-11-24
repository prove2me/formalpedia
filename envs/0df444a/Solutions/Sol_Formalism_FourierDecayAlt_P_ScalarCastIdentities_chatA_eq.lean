-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.chatA_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:10:57.679229+00:00
-- url     : https://prove2.me/submissions/88aa3911-b80d-4470-ad41-3f0d32f5cf8f

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
theorem _root_.solution (w : ℂ) (x ξ : Fin t → ℂ) :
    chatA E w x ξ = ∑ q, ∑ p, (ξ q * x p) • mS E q p w := by
  unfold chatA mS
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
