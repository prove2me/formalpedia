-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.regularised_pairing_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:08:46.260614+00:00
-- url     : https://prove2.me/submissions/9b7b3675-d703-4c93-a9ee-a6def2dd1829

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_oneMinusDD_const_mul

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {X Y X₁ Y₁ : Mat k r → (Wq →L[ℂ] Wp)} (a : ℂ)
    (h : ∀ q, Ph D X Y q = a * Ph D X₁ Y₁ q) (τ : ℝ × ℝ) :
    betaInfTau D τ X Y = a * betaInfTau D τ X₁ Y₁ := by
  have e : ∀ p, regBracket D X Y p = fun x y => a * regBracket D X₁ Y₁ p x y := by
    intro p
    funext x y
    unfold regBracket
    rw [h]
    ring
  unfold betaInfTau
  rw [← integral_const_mul]
  congr 1
  funext p
  rw [e p]
  simp only [oneMinusDD_const_mul, mul_assoc]
  rw [integral_const_mul]
  ring
end Formalism.FourierDecayAlt.P.B6
