-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.shift_bound2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:57.418026+00:00
-- url     : https://prove2.me/submissions/0f97721b-7906-499c-ad85-50e74a11cbb4

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
theorem _root_.solution (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) (n d : ℕ) :
    |∑ i ∈ Icc 1 n, (de (i + d) - de i)| ≤ n := by
  calc _ ≤ ∑ i ∈ Icc 1 n, |de (i + d) - de i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Icc 1 n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rcases h01 (i + d) with a | a <;> rcases h01 i with b | b <;> rw [a, b] <;> norm_num
    _ = n := by simp
end Formalism.FourierDecayAlt.P.Sz4
