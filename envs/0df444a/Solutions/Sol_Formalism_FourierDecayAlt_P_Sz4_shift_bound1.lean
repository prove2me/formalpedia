-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.shift_bound1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:06.278831+00:00
-- url     : https://prove2.me/submissions/678eb768-c817-4d2c-ae60-99bcd45b37c1

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_tele

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
    |∑ i ∈ Icc 1 n, (de (i + d) - de i)| ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h : ∑ i ∈ Icc 1 n, (de (i + (d + 1)) - de i) =
        ∑ i ∈ Icc 1 n, (de (i + d) - de i) + (de (n + 1 + d) - de (1 + d)) := by
      have := tele (fun i => de (i + d)) n
      rw [← this, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : i + (d + 1) = i + 1 + d := by ring
      rw [this]; ring
    rw [h]
    have h2 : |de (n + 1 + d) - de (1 + d)| ≤ 1 := by
      rcases h01 (n + 1 + d) with a | a <;> rcases h01 (1 + d) with b | b <;> rw [a, b] <;> norm_num
    calc _ ≤ |∑ i ∈ Icc 1 n, (de (i + d) - de i)| + |de (n + 1 + d) - de (1 + d)| := abs_add_le _ _
      _ ≤ (d : ℝ) + 1 := by linarith
      _ = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
end Formalism.FourierDecayAlt.P.Sz4
