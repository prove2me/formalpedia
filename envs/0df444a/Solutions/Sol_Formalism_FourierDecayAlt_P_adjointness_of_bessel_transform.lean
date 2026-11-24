-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.adjointness_of_bessel_transform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:39:45.53143+00:00
-- url     : https://prove2.me/submissions/b128ddfb-e269-4641-95ea-b989e0eb70c8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded

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
theorem _root_.solution : Formalism.FourierDecayAlt.B.AssembleAdj := by
  intro hPA hRP k r Wp Wq _ _ _ _ _ _ D A hB2 UU Θ hStab hSm hCom F F' hCk hCk' hS hS' h1 h2 h3 h4 hIC
  have hT : ∀ τ, betaInfTau D τ (opApply Θ F) F' = betaInfTau D τ F (opAdj Θ F') := fun τ =>
    hRP k r Wp Wq D τ _ _ _ _ (hPA k r Wp Wq D UU Θ hStab hSm hCom F F' hCk hCk' hS hS' hIC)
  rw [hB2 _ _ h3 h2, hB2 _ _ h1 h4]
  first
  | (unfold betaInf; simp only [hT])
  | (simp only [betaInf, hT])
  | (unfold betaInf; rw [hT])
end Formalism.FourierDecayAlt.P
