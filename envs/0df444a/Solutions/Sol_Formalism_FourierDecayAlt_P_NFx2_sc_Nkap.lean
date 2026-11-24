-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_Nkap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:01:31.661795+00:00
-- url     : https://prove2.me/submissions/b87ee0ef-6c68-4641-b327-11973fef061f

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_Bkap

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (b : M.Ty P → A) (f : M.Ty P → ℂ) :
    κ f * nabDef L0 κ b = nabDef L0 κ b * κ f := by
  have hZ : κ f * (L0.ζb * L0.GGi) = (L0.ζb * L0.GGi) * κ f := by
    rw [← mul_assoc, sc_kc h f (sc_mζb L0), mul_assoc, sc_kc h f (sc_mGGi L0), mul_assoc]
  rw [sc_N_eq, mul_sub, sub_mul, mul_neg, neg_mul, sc_Bkap, mul_smul_comm, smul_mul_assoc, hZ]
end Formalism.FourierDecayAlt.P.NFx2
