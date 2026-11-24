-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x5.colEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:39:21.048043+00:00
-- url     : https://prove2.me/submissions/70043bd7-d1b8-49b0-9e0b-cd035b72857c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x5
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {s : B.Mat k r} {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (h : s * Fm k r z = Fm k r z * U) (b : Fin (r + 1)) :
    s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c := by
  funext i
  have := congrFun (congrFun h i) b
  simp only [Matrix.mul_apply, Fm, Matrix.of_apply] at this
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
end Formalism.FourierDecayAlt.P.C2x5
