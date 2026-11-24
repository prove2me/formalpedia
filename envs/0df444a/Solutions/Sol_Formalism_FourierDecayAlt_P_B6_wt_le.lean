-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.wt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:21.456985+00:00
-- url     : https://prove2.me/submissions/eaa07c75-325c-46e6-bf18-b2f0ad765013

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_lorentzian_weight_bound

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {τ : ℝ × ℝ} (h1 : 0 < τ.1) (h2 : 0 < τ.2) (p : SS k r) :
    wt D τ p ≤ 4 * max 1 (τ.1 ^ 2)⁻¹ * max 1 (τ.2 ^ 2)⁻¹ * LL D p := by
  have a1 := lorentzian_weight_bound h1 (lam k r D.z (Matrix.of p.1.2))
  have a2 := lorentzian_weight_bound h2 (lam k r D.z' (Matrix.of p.2.2))
  unfold wt LL
  calc _ ≤ (2 * max 1 (τ.1 ^ 2)⁻¹ * (1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-2 : ℝ)) *
        (2 * max 1 (τ.2 ^ 2)⁻¹ * (1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-2 : ℝ)) :=
        mul_le_mul a1 a2 (by positivity) (by positivity)
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.B6
