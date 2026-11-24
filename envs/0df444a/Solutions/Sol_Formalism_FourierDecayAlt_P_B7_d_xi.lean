-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:17:39.856582+00:00
-- url     : https://prove2.me/submissions/a8b90e54-38f1-46b5-a51e-765805e8ad91

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_lam

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (τ t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (p : SS k r) :
    xiTau D τ (dilation₂ t p) = xiTau D (τ.1 * t.1, τ.2 * t.2) p := by
  unfold xiTau dilation₂
  have e1 : lam k r D.z (Matrix.of (conjM (aDil k r t.1) p.1.2)) = t.1 * lam k r D.z (Matrix.of p.1.2) :=
    d_lam D.z D.z_mem t.1 h1 _
  have e2 : lam k r D.z' (Matrix.of (conjM (aDil k r t.2) p.2.2)) = t.2 * lam k r D.z' (Matrix.of p.2.2) :=
    d_lam D.z' D.z'_mem t.2 h2 _
  simp only [e1, e2, mul_assoc]
end Formalism.FourierDecayAlt.P.B7
