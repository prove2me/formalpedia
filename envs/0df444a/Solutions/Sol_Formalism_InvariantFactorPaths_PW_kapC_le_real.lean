-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.kapC_le_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:55.801371+00:00
-- url     : https://prove2.me/submissions/bb8ac7dc-941a-4c06-96c9-fb9ab631f624

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (p : ℕ) [Fact p.Prime] (r d a : ℕ) (h : d + r ≤ p ^ 2 * (8 * a + r) ^ 2) :
    (kapC p r d : ℝ) ≤ (r : ℝ) ^ 2 * lgV2 p a r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp [kapC]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hx : (1 : ℝ) ≤ 8 * a + r := by exact_mod_cast (by omega : 1 ≤ 8 * a + r)
  have hlg : 0 ≤ lgV2 p a r := by
    unfold lgV2
    have := Real.logb_nonneg hp1 hx
    linarith
  have hL : ((Nat.log p (d + r - 1) : ℕ) : ℝ) ≤ 2 * lgV2 p a r := by
    by_cases hD : d + r - 1 = 0
    · rw [hD, Nat.log_zero_right]
      simp only [CharP.cast_eq_zero]
      linarith
    have hpos : (0 : ℝ) < ((d + r - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD
    have hpow : (p : ℝ) ^ (Nat.log p (d + r - 1)) ≤ ((d + r - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self p hD
    have h1 : ((Nat.log p (d + r - 1) : ℕ) : ℝ) ≤ Real.logb p ((d + r - 1 : ℕ) : ℝ) := by
      rw [Real.le_logb_iff_rpow_le hp1 hpos, Real.rpow_natCast]
      exact hpow
    have h2 : ((d + r - 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ 2 * (8 * a + r) ^ 2 := by
      exact_mod_cast (Nat.sub_le _ _).trans h
    have h3 := Real.logb_le_logb_of_le hp1 hpos h2
    have h4 : Real.logb p ((p : ℝ) ^ 2 * (8 * a + r) ^ 2) = 2 + 2 * Real.logb p (8 * a + r) := by
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
        Real.logb_self_eq_one hp1]
      push_cast
      ring
    unfold lgV2
    linarith
  have hc : ((r.choose 2 : ℕ) : ℝ) * 2 ≤ (r : ℝ) ^ 2 := by
    have hn : r.choose 2 * 2 ≤ r ^ 2 := by
      rw [Nat.choose_two_right]
      calc r * (r - 1) / 2 * 2 ≤ r * (r - 1) := Nat.div_mul_le_self _ _
        _ ≤ r ^ 2 := by
          rw [sq]
          exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    exact_mod_cast hn
  unfold kapC
  push_cast
  calc ((r.choose 2 : ℕ) : ℝ) * ((Nat.log p (d + r - 1) : ℕ) : ℝ)
      ≤ ((r.choose 2 : ℕ) : ℝ) * (2 * lgV2 p a r) := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
    _ = (((r.choose 2 : ℕ) : ℝ) * 2) * lgV2 p a r := by ring
    _ ≤ (r : ℝ) ^ 2 * lgV2 p a r := mul_le_mul_of_nonneg_right hc hlg
end Formalism.InvariantFactorPaths.PW
