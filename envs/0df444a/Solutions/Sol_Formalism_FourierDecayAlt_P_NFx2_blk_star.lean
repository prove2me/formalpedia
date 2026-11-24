-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.blk_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:19:45.186805+00:00
-- url     : https://prove2.me/submissions/88bbd49a-4ed1-45a6-a675-91e24d339b48

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
theorem _root_.solution {R : M.Ty P → M.Ty P → Prop} {X : A} (hs : ∀ ρ, star (proj κ ρ) = proj κ ρ) (hX : GlobalTheory κ R X) :
    GlobalTheory κ (fun τ σ => R σ τ) (star X) := by
  intro σ τ h
  have := hX τ σ h
  have e := congrArg star this
  rw [star_mul, star_mul, hs, hs, star_zero, ← mul_assoc] at e
  exact e
end Formalism.FourierDecayAlt.P.NFx2
