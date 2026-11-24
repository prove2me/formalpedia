-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.pr_alg_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:31:30.603609+00:00
-- url     : https://prove2.me/submissions/8e12d24a-3a6e-4764-ac86-f8a53788a79d

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
theorem _root_.solution (w : ℂ) : (algebraMap ℂ (Pr V) w).1 = algebraMap ℂ (Module.End ℂ V) w := rfl
end Formalism.FourierDecayAlt.P5
