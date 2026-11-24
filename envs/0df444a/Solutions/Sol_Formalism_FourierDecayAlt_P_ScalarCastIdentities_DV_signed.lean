-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.DV_signed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:33:48.285253+00:00
-- url     : https://prove2.me/submissions/76c2c6a6-45b5-4da5-b9de-7bb59e7d648d

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_cast_mul_eq_smul
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
variable {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution (hD : DetVec) (hE : GlRel E) (y : Fin t → A) (hy : IsVec E y) (w : ℂ) (j : Fin t) :
    qdet E w * y j = y j * qdet E w - ∑ l, y l * mS E j l w := by
  rw [hD A t E y hE hy w j]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [cast_mul_eq_smul, mS, mul_smul_comm]
  push_cast
  rfl
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
