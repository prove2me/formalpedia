-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.product_bound_monotone_factors_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:07:17.141801+00:00
-- url     : https://prove2.me/submissions/c984e594-8aa7-497e-940b-2e6c6eff65e4

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

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
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {e c P M' K c₀ M m : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 + K) (hc0 : 0 ≤ c) (hc : c ≤ c₀)
    (hP : 0 ≤ P) (hM0 : 0 ≤ M') (hM : M' ≤ 1 + M) (hm : 0 ≤ m) :
    e * (c * P * M' * m) ≤ (1 + K) * c₀ * P * (1 + M) * m := by
  have h1 : e * c ≤ (1 + K) * c₀ := mul_le_mul he hc hc0 (le_trans he0 he)
  have h2 : e * c * P ≤ (1 + K) * c₀ * P := mul_le_mul_of_nonneg_right h1 hP
  have h3 : e * c * P * M' ≤ (1 + K) * c₀ * P * (1 + M) :=
    mul_le_mul h2 hM hM0 (le_trans (mul_nonneg (mul_nonneg he0 hc0) hP) h2)
  calc e * (c * P * M' * m) = e * c * P * M' * m := by ring
    _ ≤ (1 + K) * c₀ * P * (1 + M) * m := mul_le_mul_of_nonneg_right h3 hm
end Formalism.FourierDecayAlt.P.B6
