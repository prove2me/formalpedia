-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.kap_mul_pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:13:43.153916+00:00
-- url     : https://prove2.me/submissions/67c186f7-32d6-407e-acd8-bb6af74934c0

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
theorem _root_.solution (f : M.Ty P → ℂ) (ρ : M.Ty P) : κ f * proj κ ρ = f ρ • proj κ ρ := by
  unfold proj
  rw [← map_mul, ← map_smul]; congr 1; funext x; by_cases hx : x = ρ <;> simp [hx]
end Formalism.FourierDecayAlt.P.NFx2
