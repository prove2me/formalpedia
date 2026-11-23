-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.rot_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:41.02783+00:00
-- url     : https://prove2.me/submissions/677c3dcc-2dbe-434f-a170-46ca4796dc73

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution (a b : ℝ) (m : ℕ) (y z : ℝ) (h : y ^ 2 + z ^ 2 = 1) :
    (a * y + b * z) ^ m = (rot a b m).1.eval y + z * (rot a b m).2.eval y := by
  induction m with
  | zero => simp [rot]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [rot, eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_one, eval_pow]
    linear_combination (b * (rot a b m).2.eval y) * h
end Formalism.FourierDecayAlt.P.Markov
