-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.blk_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:33.290239+00:00
-- url     : https://prove2.me/submissions/d8358c66-5674-4da5-8299-42cf7d2ba93b

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
theorem _root_.solution (X Y : A) (σ τ : M.Ty P) :
    proj κ σ * (X * Y) * proj κ τ = ∑ μ, (proj κ σ * X * proj κ μ) * (proj κ μ * Y * proj κ τ) := by
  have : X * Y = X * (∑ μ, proj κ μ) * Y := by rw [sum_pj, mul_one]
  rw [this, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : proj κ μ = proj κ μ * proj κ μ := (pj_idem κ μ).symm
  conv_lhs => rw [e]
  noncomm_ring
end Formalism.FourierDecayAlt.P.NFx2
