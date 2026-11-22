-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.mkP_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:33.106842+00:00
-- url     : https://prove2.me/submissions/d24f43f5-4192-4f6a-834b-26b674246f0d

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
open Polynomial
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (m : ℕ) (c : ℕ → ℂ) (z : ℂ) : (mkP m c).eval z = ∑ q ∈ range (m + 1), z ^ q * c q := by
  unfold mkP
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]
end Formalism.FourierDecayAlt.P.LEx2
