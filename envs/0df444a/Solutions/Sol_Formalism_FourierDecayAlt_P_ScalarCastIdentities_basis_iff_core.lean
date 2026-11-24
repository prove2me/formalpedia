-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.basis_iff_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:32:29.460823+00:00
-- url     : https://prove2.me/submissions/9c6b6455-7737-4b07-b24f-005aaddf5827

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_chY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_chX_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_chYY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_chatA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_secondChern_eq_double_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_single_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_sum_single_single_smul

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
theorem _root_.solution (y η : Fin t → A) (u : ℂ) (p q : Fin t) :
    (qdet E (u + 1) * ch2 E (u - 1) y (Pi.single p 1) η (Pi.single q 1) +
          chY E (u + 1) y (Pi.single q 1) * chX E (u - 1) (Pi.single p 1) η =
        chYY E u y η * chatA E u (Pi.single p 1) (Pi.single q 1)) ↔ Core E y η u p q := by
  rw [secondChern_eq_double_sum, chY_eq, chX_eq, chYY_eq, chatA_eq, sum_single_single_smul, single_sum, single_sum, sum_single_single_smul]
  exact Iff.rfl
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
