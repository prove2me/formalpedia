-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.connection_coordinate_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:45:25.531385+00:00
-- url     : https://prove2.me/submissions/208ca817-ed04-4d04-a21f-1475b7380089

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_Nskap
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_raising_constant_eq

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    xA κ Y * (sc_LL h hF).m0 Y = (sc_LL h hF).m0 Y * xA κ Y := by
  unfold xA
  rw [connection_raising_constant_eq, mul_sub, sub_mul, mul_neg, neg_mul, sc_Nskap h, mul_smul_comm, smul_mul_assoc, ← mul_assoc,
    sc_kc h _ (sc_mζ L0), mul_assoc, sc_kc h _ (sc_mGGi L0), mul_assoc]
end Formalism.FourierDecayAlt.P.NFx2
