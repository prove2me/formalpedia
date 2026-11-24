-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.oneMinusDD_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:06:55.883441+00:00
-- url     : https://prove2.me/submissions/ea714cd8-e20a-471e-b796-f78730d179f9

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
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {h₁ h₂ : ℝ → ℝ → ℂ} (a₁ : ∀ x, ContDiff ℝ 2 (fun y => h₁ x y))
    (a₂ : ∀ x, ContDiff ℝ 2 (fun y => h₂ x y))
    (b₁ : ∀ y, ContDiff ℝ 2 (fun x => h₁ x y - iteratedDeriv 2 (fun y' => h₁ x y') y))
    (b₂ : ∀ y, ContDiff ℝ 2 (fun x => h₂ x y - iteratedDeriv 2 (fun y' => h₂ x y') y)) (x y : ℝ) :
    oneMinusDD (fun x y => h₁ x y + h₂ x y) x y = oneMinusDD h₁ x y + oneMinusDD h₂ x y := by
  have i1 : ∀ x y, iteratedDeriv 2 (fun y' => h₁ x y' + h₂ x y') y =
      iteratedDeriv 2 (fun y' => h₁ x y') y + iteratedDeriv 2 (fun y' => h₂ x y') y := fun x y =>
    iteratedDeriv_fun_add (a₁ x).contDiffAt (a₂ x).contDiffAt
  have i2 : (fun x => (h₁ x y + h₂ x y) - iteratedDeriv 2 (fun y' => h₁ x y' + h₂ x y') y) =
      fun x => (h₁ x y - iteratedDeriv 2 (fun y' => h₁ x y') y) +
        (h₂ x y - iteratedDeriv 2 (fun y' => h₂ x y') y) := by
    funext x; rw [i1]; ring
  unfold oneMinusDD
  simp only []
  rw [i2, i1, iteratedDeriv_fun_add (b₁ y).contDiffAt (b₂ y).contDiffAt]
  ring
end Formalism.FourierDecayAlt.P.B6
