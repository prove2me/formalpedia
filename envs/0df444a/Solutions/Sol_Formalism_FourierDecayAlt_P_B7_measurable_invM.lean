-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.measurable_invM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:54:07.36867+00:00
-- url     : https://prove2.me/submissions/cecd10d7-eb9b-4706-b9ce-3909d3e41417

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

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
theorem _root_.solution : Measurable (invM (k := k) (r := r)) := by
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  have hdet : Measurable fun x : Mt k r => (Matrix.of x : Mat k r).det := hc.matrix_det.measurable
  have hadj : ∀ i j, Measurable fun x : Mt k r => (Matrix.of x : Mat k r).adjugate i j := fun i j =>
    ((continuous_apply j).comp ((continuous_apply i).comp hc.matrix_adjugate)).measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [invM, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  exact (measurable_inv.comp hdet).mul (hadj i j)
end Formalism.FourierDecayAlt.P.B7
