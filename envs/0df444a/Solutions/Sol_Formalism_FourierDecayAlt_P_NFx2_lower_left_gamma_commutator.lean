-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.lower_left_gamma_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:21:23.602066+00:00
-- url     : https://prove2.me/submissions/a1677a95-aac2-4e7c-82fd-d9c1b6dd6dce

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (v : ℂ) :
    QQ v 1 0 * L0.GG = L0.GG * QQ v 1 0 - QQ v 1 1 * L0.ζb := by
  obtain ⟨e1, -, -, -, e5, -⟩ := levelSubgroupAtPlace h v
  have e2 : QQ v 1 0 * algebraMap ℂ A L0.TT = algebraMap ℂ A L0.TT * QQ v 1 0 := (Algebra.commutes _ _).symm
  rw [L0.GG_def, mul_sub, sub_mul, e2, ← mul_assoc, e1, sub_mul, mul_assoc, e5]
  noncomm_ring
end Formalism.FourierDecayAlt.P.NFx2
