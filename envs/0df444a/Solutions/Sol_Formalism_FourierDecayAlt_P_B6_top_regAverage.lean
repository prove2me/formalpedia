-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.top_regAverage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:13.212919+00:00
-- url     : https://prove2.me/submissions/df9c1d98-8ff7-498d-9932-413f0fe453cc

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regAverage_of_hyp
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_top_ph_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_top_beta_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_top_hyp

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
theorem _root_.solution (hN : DilN) (hU : DilUW) : StepRegAverage := by
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hA h1 h2 hJ
  rcases subsingleton_or_nontrivial (Wq →L[ℂ] Wp) with hs | hn
  · intro F F' _ _ w₁ w₂ _ _
    simp only [top_beta_zero, top_ph_zero]
    simp
  · exact regAverage_of_hyp (top_hyp hN hU hA h1 h2) hJ
end Formalism.FourierDecayAlt.P.B6
