-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.positionProduct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:13.036528+00:00
-- url     : https://prove2.me/submissions/7d0c083e-4337-44f4-93ce-a15f56315a70

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : ProdOneAddTwoDivLeSqrt := by
  have key : ∀ p : ℕ, 1 ≤ p → 0 ≤ ∏ j ∈ Icc 1 p, (1 + 2 / (4 * (j : ℝ) - 1)) ∧
      (∏ j ∈ Icc 1 p, (1 + 2 / (4 * (j : ℝ) - 1))) ^ 2 ≤ 50 / 27 * ((p:ℝ) + 1 / 2) := by
    intro p hp
    induction p, hp using Nat.le_induction with
    | base => simp; norm_num
    | succ n hn ih =>
      obtain ⟨ih0, ih1⟩ := ih
      rw [Finset.prod_Icc_succ_top (by omega)]
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have e : 1 + 2 / (4 * ((n + 1 : ℕ) : ℝ) - 1) = (4 * (n:ℝ) + 5) / (4 * (n:ℝ) + 3) := by
        have h4 : 4 * ((n:ℝ) + 1) - 1 ≠ 0 := by nlinarith
        push_cast; field_simp; ring
      rw [e]
      refine ⟨mul_nonneg ih0 (by positivity), ?_⟩
      rw [mul_pow, div_pow]
      have h3 : 0 < (4 * (n:ℝ) + 3) ^ 2 := by positivity
      rw [mul_div_assoc', div_le_iff₀ h3]
      push_cast
      have := mul_le_mul_of_nonneg_right ih1 (by positivity : (0:ℝ) ≤ (4 * (n:ℝ) + 5) ^ 2)
      nlinarith
  intro p hp
  obtain ⟨h0, h1⟩ := key p hp
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hs : 0 ≤ 3.3 * Real.sqrt p := by positivity
  refine (pow_le_pow_iff_left₀ h0 hs (two_ne_zero)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  norm_num
  linarith
end Formalism.FourierDecayAlt.P
