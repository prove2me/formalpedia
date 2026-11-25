-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lattice_x_eq_lambda_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:34.776294+00:00
-- url     : https://prove2.me/submissions/10e36a0c-7da9-447c-990d-81daca8fa502

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.XIsLamOne := by
  intro m i C ka N I A g B
  have h : 2 * (i - 1) + 1 - 1 = 2 * i - 2 := by omega
  refine ⟨?_, ?_⟩
  · unfold Sz.xThreshold Sz.lamThreshold
    rw [h]
  · unfold Sz.xHat Sz.lamHat
    rw [h]
end Formalism.FourierDecayAlt.P
