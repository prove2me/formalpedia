-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.commute_mkP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:09:12.296942+00:00
-- url     : https://prove2.me/submissions/0d2c53de-05d5-4991-8f21-38e34e4500fd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution {A B C D : Module.End ℂ V} (h1 : A * C = C * A) (h2 : D * B = B * D) :
    Commute (mkP A B : Pr V) (mkP C D) := by
  show ((A * C, MulOpposite.op B * MulOpposite.op D) : Module.End ℂ V × (Module.End ℂ V)ᵐᵒᵖ) =
    (C * A, MulOpposite.op D * MulOpposite.op B)
  rw [h1, ← MulOpposite.op_mul, ← MulOpposite.op_mul, h2]
end Formalism.FourierDecayAlt.P5
