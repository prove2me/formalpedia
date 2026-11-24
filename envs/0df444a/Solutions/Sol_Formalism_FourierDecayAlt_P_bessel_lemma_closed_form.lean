-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.bessel_lemma_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:44.672793+00:00
-- url     : https://prove2.me/submissions/c875e7fc-2c93-42c6-bf90-d6f9a842cd15

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
theorem _root_.solution : Formalism.FourierDecayAlt.B.LemmaBClosedFromParts := by
  intro hXi hLB hSC hAP k r Wp Wq _ _ _ _ _ _ D A hA hInt hConj hDJ hCCI
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  have h0A : 0 ≤ A := (B2.AB_nonneg k r).trans hA
  obtain ⟨h1, h2, h3⟩ := hLB k r Wp Wq D Ξ A hA hInt hConj hDJ hCCI hCB hXI
  exact ⟨h1, h2, h3, hAP hSC k r Wp Wq D A h0A hCCI h3⟩
end Formalism.FourierDecayAlt.P
