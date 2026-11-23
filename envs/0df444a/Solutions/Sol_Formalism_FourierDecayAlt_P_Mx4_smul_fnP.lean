-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.smul_fnP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:22.717207+00:00
-- url     : https://prove2.me/submissions/3ed1caf3-cc00-499a-aa6c-c395fd88b0e4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (a : ℝ) (f fb : Fn r) : (a : ℂ) • fnP f fb = fnP ((a : ℂ) • f) ((a : ℂ) • fb) := by
  rw [Algebra.smul_def]
  refine Prod.ext ?_ ?_
  · show algebraMap ℂ (Op r) a * mulOp f = mulOp ((a : ℂ) • f)
    ext h : 1; simp [mulOp]
  · show (algebraMap ℂ (Op r)ᵐᵒᵖ) (starRingEnd ℂ (a : ℂ)) * MulOpposite.op (mulOp fb) = MulOpposite.op (mulOp ((a : ℂ) • fb))
    rw [Complex.conj_ofReal, ← Algebra.smul_def, ← MulOpposite.op_smul]
    congr 1
    ext h : 1; simp [mulOp]
end Formalism.FourierDecayAlt.P.Mx4
