-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:46.728837+00:00
-- url     : https://prove2.me/submissions/e0ab9514-4bdd-4e5d-b0a0-6a20972e34cc

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2_aDil_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (t : ℝ) (ht : t ≠ 0) (n : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (aDil k r t * n * (aDil k r t)⁻¹) i j = d_dg k r t i * n i j * d_dg k r t⁻¹ j := by
  rw [Formalism.FourierDecayAlt.P.B2.aDil_inv k r t ht, d_aDil_eq, d_aDil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
end Formalism.FourierDecayAlt.P.B7
