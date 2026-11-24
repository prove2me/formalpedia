-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.H_rtt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:30.262807+00:00
-- url     : https://prove2.me/submissions/1a4f5c68-b530-4fd7-b42c-e9de0afbdc7e

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_H_start
import Theorems.Thm_Formalism_FourierDecayAlt_P_rtt_relation_entries


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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (u v : ℂ) (i j k l : Fin 2) :
    (u - v) • (QQ u i j * QQ v k l - QQ v k l * QQ u i j) = QQ u k j * QQ v i l - QQ v k j * QQ u i l :=
  Formalism.FourierDecayAlt.P.rtt_relation_entries ℂ A QQ v u ((H_start h).rtt v u) i j k l
end Formalism.FourierDecayAlt.P.NFx2
