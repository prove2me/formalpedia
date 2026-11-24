-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.kappa_commute_raising
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:44:05.124513+00:00
-- url     : https://prove2.me/submissions/aea1eeff-a52d-4350-bea9-f8c32d4f9f53

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kz
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_knabs
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kalg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (f : M.Ty P → ℂ) (Y : ℂ) : Commute (κ f) (L.m0 Y) := by
  unfold R.LevelData.m0
  exact ((sn_knabs hc f).neg_right).sub_right ((sn_kalg f _).mul_right ((sn_kz hc f).mul_right (sn_kGi hc f)))
end Formalism.FourierDecayAlt.P.NFx2
