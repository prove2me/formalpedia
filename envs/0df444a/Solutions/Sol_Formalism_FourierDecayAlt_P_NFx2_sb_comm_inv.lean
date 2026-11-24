-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_comm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:19:48.894246+00:00
-- url     : https://prove2.me/submissions/0d55e9df-b85a-4552-be0a-846846a4971e

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
theorem _root_.solution {X a ai : A} (h : Commute X a) (h1 : a * ai = 1) (h2 : ai * a = 1) : Commute X ai := by
  show X * ai = ai * X
  calc X * ai = (ai * a) * X * ai := by rw [h2, one_mul]
    _ = ai * (a * X) * ai := by noncomm_ring
    _ = ai * (X * a) * ai := by rw [h.eq]
    _ = ai * X * (a * ai) := by noncomm_ring
    _ = ai * X := by rw [h1, mul_one]
end Formalism.FourierDecayAlt.P.NFx2
