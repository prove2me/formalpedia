-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:55.174111+00:00
-- url     : https://prove2.me/submissions/a623c4e2-8f08-44a3-a943-8a99cc7a1e7a

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_raises
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_SS_comm

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
theorem _root_.solution : SBlock := by
  intro _ _ _ P A _ _ _ L0 QQ κ hP h
  exact ⟨sb_b L0 κ QQ, sb_SS κ QQ, sb_form h hP, sb_raises, fun l => sb_SS_comm h l⟩
end Formalism.FourierDecayAlt.P.NFx2
