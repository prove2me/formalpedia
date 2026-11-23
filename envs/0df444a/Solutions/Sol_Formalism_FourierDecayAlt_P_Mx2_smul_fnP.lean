-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.smul_fnP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:02.330975+00:00
-- url     : https://prove2.me/submissions/a2a250b0-2901-4b9b-9b2a-4fe05cb3c30c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution (a : ℝ) (f fb : Fn r) : (a : ℂ) • fnP f fb = fnP ((a : ℂ) • f) ((a : ℂ) • fb) := by
  rw [Algebra.smul_def]
  refine Prod.ext ?_ ?_
  · show algebraMap ℂ (Op r) a * mulOp f = mulOp ((a : ℂ) • f)
    ext h : 1; simp [mulOp]
  · show (algebraMap ℂ (Op r)ᵐᵒᵖ) (starRingEnd ℂ (a : ℂ)) * MulOpposite.op (mulOp fb) = MulOpposite.op (mulOp ((a : ℂ) • fb))
    rw [Complex.conj_ofReal, ← Algebra.smul_def, ← MulOpposite.op_smul]
    congr 1
    ext h : 1; simp [mulOp]
end Formalism.FourierDecayAlt.P.Mx2
