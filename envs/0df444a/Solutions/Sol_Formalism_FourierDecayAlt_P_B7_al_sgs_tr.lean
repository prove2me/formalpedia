-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.al_sgs_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:08:41.482798+00:00
-- url     : https://prove2.me/submissions/b5142c30-c78d-4aba-aa5a-b305c11ee2bf

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution {p' p : SS k r} (u1 : IsUnit (Matrix.of p'.1.1 : Mat k r).det)
    (u3 : IsUnit (Matrix.of p'.2.1 : Mat k r).det) (g : Mat k r) :
    sgs (tr p' p) g = sgs p (sgs p' g) := by
  show (Matrix.of p'.1.1 * Matrix.of p.1.1)⁻¹ *
      (Matrix.of p'.1.2 * (Matrix.of p'.1.1 * Matrix.of p.1.2 * (Matrix.of p'.1.1)⁻¹))⁻¹ * g *
      (Matrix.of p'.2.2 * (Matrix.of p'.2.1 * Matrix.of p.2.2 * (Matrix.of p'.2.1)⁻¹)) *
      (Matrix.of p'.2.1 * Matrix.of p.2.1) =
    (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ *
      ((Matrix.of p'.1.1)⁻¹ * (Matrix.of p'.1.2)⁻¹ * g * Matrix.of p'.2.2 * Matrix.of p'.2.1) *
      Matrix.of p.2.2 * Matrix.of p.2.1
  simp only [Matrix.mul_assoc, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ u1,
    Matrix.nonsing_inv_mul_cancel_left _ _ u1, Matrix.nonsing_inv_mul_cancel_left _ _ u3]
end Formalism.FourierDecayAlt.P.B7
