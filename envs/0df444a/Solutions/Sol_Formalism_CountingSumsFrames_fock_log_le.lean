-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fock_log_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:34.880654+00:00
-- url     : https://prove2.me/submissions/29ad3d49-303b-434f-800e-55e00a692c98

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_fock_L_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (k D : ℕ) (a : ℝ) (ha : 0 ≤ a) (hk : 1 ≤ k)
    (hD : (D : ℝ) ≤ 2 * a) : (Nat.log p D : ℝ) ≤ Real.logb p (2 * a + k) + 1 := by
  have h0 := fock_L_nonneg p k a ha hk
  rcases Nat.eq_zero_or_pos D with hD0 | hD0
  · subst hD0; simpa using h0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < 2 * a + k := by linarith
  have hle : (Nat.log p D : ℝ) ≤ Real.logb p (2 * a + k) := by
    rw [Real.le_logb_iff_rpow_le hp1 hpos, Real.rpow_natCast]
    have : p ^ Nat.log p D ≤ D := Nat.pow_log_le_self p hD0.ne'
    have : ((p ^ Nat.log p D : ℕ) : ℝ) ≤ D := by exact_mod_cast this
    push_cast at this
    linarith
  linarith
end Formalism.CountingSumsFrames
