-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_lreg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:22:54.50594+00:00
-- url     : https://prove2.me/submissions/8c7cdf18-5d4b-4baf-8c95-bba8dcbfc257

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_xA_xiA

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
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) {Y : ℂ} (hY : Reg P Y) : QQ Y 1 0 = L0.GG * xA κ Y * lA L0 QQ κ Y := by
  unfold lA
  have e : L0.GG * xA κ Y * (xiA κ Y * L0.GGi * QQ Y 1 0) = L0.GG * (xA κ Y * xiA κ Y) * L0.GGi * QQ Y 1 0 := by
    noncomm_ring
  rw [e, xA_xiA κ hY, mul_one, L0.GG_GGi, one_mul]
end Formalism.FourierDecayAlt.P.NFx2
