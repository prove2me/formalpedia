-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_hsVec_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:12:48.888017+00:00
-- url     : https://prove2.me/submissions/69268b76-5b00-4f7f-b939-520ee6aeee2f

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution [FiniteDimensional ℂ Wq] (x : ℝ) (A : Wq →L[ℂ] Wp) :
    ‖hsVec (x • A)‖ = |x| * ‖hsVec A‖ := by
  have e : hsVec (x • A) = x • hsVec A := by
    first
      | (ext i; simp [hsVec])
      | (unfold hsVec; rw [← WithLp.toLp_smul]; congr 1; funext i; simp)
  rw [e, norm_smul, Real.norm_eq_abs]
end Formalism.FourierDecayAlt.P.B7
