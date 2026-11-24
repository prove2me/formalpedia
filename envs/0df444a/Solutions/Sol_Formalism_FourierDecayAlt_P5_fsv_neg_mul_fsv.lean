-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.fsv_neg_mul_fsv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:48:24.512737+00:00
-- url     : https://prove2.me/submissions/9c69bc67-2b41-4b82-a5e8-3875ced345e6

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Theorems.Thm_Formalism_FourierDecayAlt_P5_fsv_mul_fsv_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (s t : ℂ) : fsv (-s) t * fsv s t = 1 := by
  rw [mul_comm]
  exact fsv_mul_fsv_neg s t
end Formalism.FourierDecayAlt.P5
