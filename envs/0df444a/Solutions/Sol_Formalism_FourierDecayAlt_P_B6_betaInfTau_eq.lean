-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.betaInfTau_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:59:01.14596+00:00
-- url     : https://prove2.me/submissions/72371951-25d4-4065-8c38-9d996ae19b31

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_E_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Et_eq

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) : betaInfTau D τ F F' = ∫ p, Gt D F F' τ p ∂D.μSS := by
  unfold betaInfTau
  refine integral_congr_ae ?_
  filter_upwards [ae_inSS D] with p hp
  unfold Gt wt phase
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only []
  rw [E_formula H hF hF' hp t, Et_eq D F F' hp t]
end Formalism.FourierDecayAlt.P.B6
