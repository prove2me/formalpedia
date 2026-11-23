-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.geom_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.095863+00:00
-- url     : https://prove2.me/submissions/89960c43-461e-428b-893b-929121bc4a0a

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real
namespace Formalism.FourierDecayAlt.P.Rec
theorem _root_.solution (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1/2) :
    ∀ i : ℕ, ∑ t ∈ Icc 2 i, a ^ (t-1) ≤ 2 * a := by
  have aux : ∀ k : ℕ, ∑ t ∈ Icc 2 (k+1), a ^ (t-1) + 2 * a ^ (k+1) ≤ 2 * a := by
    intro k
    induction k with
    | zero =>
      rw [Finset.Icc_eq_empty (by norm_num)]
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have e : k + 1 + 1 - 1 = k + 1 := by omega
      rw [e]
      have hp := pow_nonneg h0 (k+1)
      have hs : a ^ (k + 1 + 1) = a ^ (k+1) * a := pow_succ a (k+1)
      rw [hs]
      nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  intro i
  rcases i with _ | k
  · rw [Finset.Icc_eq_empty (by norm_num)]; simp; linarith
  · have := aux k
    have hp := pow_nonneg h0 (k+1)
    linarith
end Formalism.FourierDecayAlt.P.Rec
