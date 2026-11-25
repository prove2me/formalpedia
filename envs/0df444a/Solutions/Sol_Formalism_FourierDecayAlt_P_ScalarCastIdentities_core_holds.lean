-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.core_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:01.019346+00:00
-- url     : https://prove2.me/submissions/9793c0c9-4f84-4cf8-b50b-1cc15e21e9c0

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_J_signed
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_DV_signed
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_MC_signed
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_covariant_commutes_signed_column_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_covariant_commutes_signed_minor_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution (hJ : QJacobi) (hD : DetVec) (hM : MinorCov) (hE : GlRel E) (y η : Fin t → A) (hy : IsVec E y)
    (hη : IsCov E η) (hc : Commute2 y η) (u : ℂ) (p q : Fin t) : Core E y η u p q := by
  have PairingFactorsThroughPeriods : ∀ j, ∑ i, η i * mS E i j u = ∑ i, mS E i j (u + 1) * η i := by
    intro j
    have := covariant_commutes_signed_column_sum E hE η hη hc.2.1 j (u + 1)
    rwa [add_sub_cancel_right] at this
  exact core y η (qdet E (u + 1)) (fun i j => mS E i j (u + 1)) (fun i j => mS E i j u) (fun i j => mS E i j (u - 1))
    (fun a q c p => nS E a q c p u) (fun a q c p => nS E a q c p (u - 1)) hc.2.2
    (fun i q l p => J_signed E hJ hE u i q l p) (fun j => DV_signed E hD hE y hy (u + 1) j)
    (fun q p i => MC_signed E hM hE η hη u q p i) (fun j => covariant_commutes_signed_column_sum E hE η hη hc.2.1 j u) PairingFactorsThroughPeriods
    (fun q c p => covariant_commutes_signed_minor_sum E hE η hη hc.2.1 q c p u) q p
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
