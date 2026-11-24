-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.regularised_pairing_via_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:46.038061+00:00
-- url     : https://prove2.me/submissions/5498003b-b860-4779-b5b6-03f933774490

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_dil_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_chi_ne

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B5
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.StepRegPh := by
  intro k r Wp Wq _ _ _ _ _ _ D τ F₁ F₁' F₂ F₂' h
  unfold betaInfTau
  apply integral_congr_ae
  filter_upwards [ae_inSS D] with p hp
  have hreg : regBracket D F₁ F₁' p = regBracket D F₂ F₂' p := by
    funext t₁ t₂
    unfold regBracket
    by_cases h0 : D.χ t₁ * D.χ t₂ = 0
    · simp [h0]
    · have h1 : D.χ t₁ ≠ 0 := left_ne_zero_of_mul h0
      have h2 : D.χ t₂ ≠ 0 := right_ne_zero_of_mul h0
      rw [h _ (dil_inSS D hp (chi_ne D h1) (chi_ne D h2))]
  simp only [hreg]
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.B5
