-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.lower_diagonal_shift_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:21:22.453795+00:00
-- url     : https://prove2.me/submissions/fad04809-e758-4583-b52c-0c00776cc3e4

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_H_start

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (Y : ℂ) : QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0 := by
  have := congrFun (congrFun ((H_start h).det Y).2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] at this
  exact sub_eq_zero.mp (by rw [← this]; noncomm_ring)
end Formalism.FourierDecayAlt.P.NFx2
