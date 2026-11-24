-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.pr_add_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:29:39.9748+00:00
-- url     : https://prove2.me/submissions/17a45cb9-feff-40d8-8429-0ce965e8024f

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (a b : Pr V) : (a + b).1 = a.1 + b.1 := rfl
end Formalism.FourierDecayAlt.P5
