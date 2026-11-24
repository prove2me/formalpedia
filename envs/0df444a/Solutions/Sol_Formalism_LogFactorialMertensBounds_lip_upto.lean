-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.lip_upto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:59.474655+00:00
-- url     : https://prove2.me/submissions/0f98306f-950d-470b-9f3c-c47e18a29be6

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Theorems.Thm_Formalism_LogFactorialMertensBounds_lipschitzConst_nonneg
import Theorems.Thm_Formalism_LogFactorialMertensBounds_lip_piece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution (k : ℕ) : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ k + 1 → 1 / 2 ≤ y → y ≤ k + 1 →
    |Gz y - Gz x| ≤ K0 * |y - x| := by
  have hK := lipschitzConst_nonneg
  induction k with
  | zero =>
    intro x y hx1 hx2 hy1 hy2
    exact lip_piece 0 x y (by rw [Nat.cast_zero]; linarith) hx1 hx2
      (by rw [Nat.cast_zero]; linarith) hy1 hy2
  | succ k ih =>
    intro x y hx1 hx2 hy1 hy2
    push_cast at hx2 hy2
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have split : ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ k + 1 → k + 1 ≤ v → v ≤ k + 1 + 1 →
        |Gz v - Gz u| ≤ K0 * |v - u| := by
      intro u v hu1 hu2 hv1 hv2
      have e1 := ih u (k + 1) hu1 hu2 (by linarith) le_rfl
      have e2 := lip_piece (k + 1) (k + 1 : ℝ) v (by push_cast; linarith) (by linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by linarith) (by push_cast; linarith)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ k + 1 - u)] at e1
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - (k + 1))] at e2
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - u)]
      calc |Gz v - Gz u| ≤ |Gz v - Gz (k + 1)| + |Gz (k + 1) - Gz u| := abs_sub_le _ _ _
        _ ≤ K0 * (v - (k + 1)) + K0 * (k + 1 - u) := add_le_add e2 e1
        _ = K0 * (v - u) := by ring
    rcases le_total x (k + 1) with hxk | hxk <;> rcases le_total y (k + 1) with hyk | hyk
    · exact ih x y hx1 hxk hy1 hyk
    · exact split x y hx1 hxk hyk hy2
    · have h := split y x hy1 hyk hxk hx2
      rwa [abs_sub_comm (Gz x), abs_sub_comm x] at h
    · exact lip_piece (k + 1) x y (by push_cast; linarith) hx1 (by push_cast; linarith)
        (by push_cast; linarith) hy1 (by push_cast; linarith)
end Formalism.LogFactorialMertensBounds
