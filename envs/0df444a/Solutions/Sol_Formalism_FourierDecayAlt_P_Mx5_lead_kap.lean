-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.lead_kap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:20.522779+00:00
-- url     : https://prove2.me/submissions/f2be12d2-673b-4d17-a12b-2158eb644a9c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (n : ℕ) (p : Ty P → ℂ[X]) (c : Ty P → ℂ) (hp : ∀ π, (p π).natDegree ≤ n)
    (hc : ∀ π, (p π).coeff n = c π) : Lead n (kap P c) fun Y => kap P fun π => (p π).eval Y := by
  refine ⟨fun i => kap P fun π => (p π).coeff i, fun Y => ?_⟩
  have e : ∀ π, (p π).eval Y = Y ^ n * c π + ∑ i ∈ range n, Y ^ i * (p π).coeff i := by
    intro π
    rw [Polynomial.eval_eq_sum_range' (show (p π).natDegree < n + 1 by have := hp π; omega), Finset.sum_range_succ, hc π,
      Finset.sum_congr rfl fun i _ => mul_comm ((p π).coeff i) (Y ^ i)]
    ring
  have e2 : (fun π => (p π).eval Y) = Y ^ n • c + ∑ i ∈ range n, Y ^ i • (fun π => (p π).coeff i) := by
    funext π
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact e π
  show kap P (fun π => (p π).eval Y) = _
  rw [e2, map_add, map_smul, map_sum]
  simp only [map_smul]
end Formalism.FourierDecayAlt.P.Mx5
