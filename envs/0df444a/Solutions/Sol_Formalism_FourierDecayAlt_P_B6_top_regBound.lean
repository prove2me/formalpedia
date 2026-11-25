-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.top_regBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:39.92811+00:00
-- url     : https://prove2.me/submissions/d8a1397b-a29d-4e8f-b186-c7500712e805

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regBound_of_hyp
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
theorem _root_.solution (hN : DilN) (hU : DilUW) : StepRegBound := by
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hA h1 h2
  rcases subsingleton_or_nontrivial (Wq →L[ℂ] Wp) with hs | hn
  · refine ⟨fun τ₀ _ => ⟨0, Set.univ, univ_mem, fun τ _ F F' c c' _ _ => ?_⟩, fun F F' _ _ => ?_,
      fun τ _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [top_beta_zero]; simp
    · simp only [top_beta_zero]; exact continuousOn_const
    all_goals intros; simp only [top_beta_zero]; simp
  · exact regBound_of_hyp (top_hyp hN hU hA h1 h2)
end Formalism.FourierDecayAlt.P.B6
