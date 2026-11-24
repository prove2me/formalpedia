-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:19:46.944858+00:00
-- url     : https://prove2.me/submissions/b5380820-1151-4a17-a16c-cfaedadabc4d

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
theorem _root_.solution (X : A) : X = ∑ σ, ∑ τ, proj κ σ * X * proj κ τ := by
  calc X = (∑ σ, proj κ σ) * X * (∑ τ, proj κ τ) := by rw [sum_pj, one_mul, mul_one]
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; simp_rw [Finset.mul_sum]
end Formalism.FourierDecayAlt.P.NFx2
