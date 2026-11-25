-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.dilationAction_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:44:30.456268+00:00
-- url     : https://prove2.me/submissions/1b135490-7ed8-422a-bbcb-a3cfbd60ca40

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_one


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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (p : SS k r) : dilation₂ (1, 1) p = p := by
  have h : ∀ x : Mt k r, conjM (aDil k r 1) x = x := by
    intro x
    unfold conjM
    rw [aDil_one, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  unfold dilation₂
  simp only [h]
end Formalism.FourierDecayAlt.P.B6
