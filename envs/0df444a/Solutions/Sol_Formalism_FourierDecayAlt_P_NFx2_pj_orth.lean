-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.pj_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:13:59.208836+00:00
-- url     : https://prove2.me/submissions/935d4ec6-236c-4e66-bbac-e3ef2db5e6db

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
theorem _root_.solution {ρ σ : M.Ty P} (h : ρ ≠ σ) : proj κ ρ * proj κ σ = 0 := by simp [pj_mul, h]
end Formalism.FourierDecayAlt.P.NFx2
