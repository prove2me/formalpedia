-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.tele
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:57.364003+00:00
-- url     : https://prove2.me/submissions/1eed31b4-1a24-4d30-9db1-f099632bfdef

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (g : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Icc 1 n, (g (i + 1) - g i) = g (n + 1) - g 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
end Formalism.FourierDecayAlt.P.Sz4
