-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.fsv_mul_fsv_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:28:32.086083+00:00
-- url     : https://prove2.me/submissions/40812a1a-08ce-49d3-ab58-990a2c2c7c49

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg

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
theorem _root_.solution (s t : ℂ) : fsv s t * fsv (-s) t = 1 := by
  rw [fsv, fsv, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_neg]
  ring
end Formalism.FourierDecayAlt.P5
