-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.bessel_lemma_from_reductions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:51.234941+00:00
-- url     : https://prove2.me/submissions/7bca5e01-28b1-4698-9a46-47571123fc12

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2_AB_nonneg

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.LemmaBFromSteps := by
  intro hFC hAe hFat hCC hDil hJ hRB hRA hU hJC hDB hPA hRP hEq hAdj
  unfold StepRegBound StepRegAverage StepUnfold StepJCont StepDilBeta at *
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hA hInt hConj hDJ hCCI hCoef hXi
  have h0A : 0 ≤ A := (B2.AB_nonneg k r).trans hA
  have h12 := hEq hFC hAe hFat hCC hDil hJ k r Wp Wq D A h0A
    (by apply hRB <;> assumption) (by apply hRA <;> assumption) (by apply hU <;> assumption)
    (by apply hJC <;> assumption) (by apply hDB <;> assumption)
  exact ⟨h12.1, h12.2, hAdj hPA hRP k r Wp Wq D A h12.2⟩
end Formalism.FourierDecayAlt.P
