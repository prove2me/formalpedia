-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.harm_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:39.429726+00:00
-- url     : https://prove2.me/submissions/d7a07e40-76f0-469f-b020-3df3d276f10e

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
theorem _root_.solution (h n : ℕ) (hh : 1 ≤ h) (hn : h ≤ n) :
    ∑ d ∈ Ioc h n, (1 : ℝ) / d ≤ Real.log n - Real.log h := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have := Real.one_sub_inv_le_log_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
    push_cast
    linarith
end Formalism.FourierDecayAlt.P.Sz4
