-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecText.geo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.454117+00:00
-- url     : https://prove2.me/submissions/7fb9c6e0-85a3-4346-8dae-405cf9176a93

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecText
open Finset Real
namespace Formalism.FourierDecayAlt.P.RecText
theorem _root_.solution (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2) :
    ∀ i, 1 ≤ i → ∑ t ∈ Icc 2 i, a ^ (t - 1) ≤ 2 * a - 2 * a ^ i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have : a ^ (n + 1) = a ^ n * a := pow_succ a n
    have h0 : 0 ≤ a ^ n := pow_nonneg ha0 n
    nlinarith
end Formalism.FourierDecayAlt.P.RecText
