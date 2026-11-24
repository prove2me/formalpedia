-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.algDet_of_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:25.956594+00:00
-- url     : https://prove2.me/submissions/8294ab64-8078-4787-be32-9321ac0a6638

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_chY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_chX_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_chYY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_chatA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_secondChern_eq_double_sum
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
theorem _root_.solution (y η : Fin t → A) (u : ℂ) (h : ∀ p q, Core E y η u p q) (x ξ : Fin t → ℂ) :
    qdet E (u + 1) * ch2 E (u - 1) y x η ξ + chY E (u + 1) y ξ * chX E (u - 1) x η =
      chYY E u y η * chatA E u x ξ := by
  rw [secondChern_eq_double_sum, chY_eq, chX_eq, chYY_eq, chatA_eq, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_smul_comm, smul_mul_smul_comm, mul_smul_comm, ← smul_add]
  congr 1
  exact h p q
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
