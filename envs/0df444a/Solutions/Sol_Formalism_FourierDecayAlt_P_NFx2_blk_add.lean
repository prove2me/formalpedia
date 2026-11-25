-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.blk_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:20.679149+00:00
-- url     : https://prove2.me/submissions/af76094b-cb15-42de-b900-c688a472add1

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {R : M.Ty P → M.Ty P → Prop} {X Y : A} (hX : GlobalTheory κ R X) (hY : GlobalTheory κ R Y) : GlobalTheory κ R (X + Y) := by
  intro σ τ h; rw [mul_add, add_mul, hX σ τ h, hY σ τ h, add_zero]
end Formalism.FourierDecayAlt.P.NFx2
