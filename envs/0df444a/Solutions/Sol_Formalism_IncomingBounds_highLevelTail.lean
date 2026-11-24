-- Prove2me | solution 1 for Formalism.IncomingBounds.highLevelTail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:13.753279+00:00
-- url     : https://prove2.me/submissions/4a9b9354-8af5-4f08-870c-bdc23539e2fb

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
section Helpers
variable {l d : ℕ} [NeZero d]
private theorem one_le_pow_of_one_le_real {a : ℝ} (ha : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith
private theorem pow_le_pow_right_of_one_le_real {a : ℝ} (ha : 1 ≤ a) {m n : ℕ} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h1 := one_le_pow_of_one_le_real ha k
  have h2 : 0 ≤ a ^ m := pow_nonneg (by linarith) m
  nlinarith
private lemma flow_out_le {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) (s : ZMod d) :
    ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i ≤ D s := by
  have h := hx.2 s
  have h0 : 0 ≤ ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
    Finset.sum_nonneg fun i _ => hx.1 _ _
  linarith
private theorem le_div_of_mul_le_of_pos_flow_degree_bounds {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  have h2 := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)
  rwa [mul_inv_cancel_right₀ hc.ne', ← div_eq_mul_inv] at h2
end Helpers
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : LevelTail := by
  intro l d _ hl D x hx i0
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hpos : (0 : ℝ) < (l : ℝ) ^ i0 := pow_pos hl0 i0
  apply le_div_of_mul_le_of_pos_flow_degree_bounds hpos
  calc (∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), x a i) * (l : ℝ) ^ i0
      = ∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), (l : ℝ) ^ i0 * x a i := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ ≤ ∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), (l : ℝ) ^ i * x a i :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (pow_le_pow_right_of_one_le_real hl1 (Finset.mem_filter.1 hi).2) (hx.1 a i)
    _ ≤ ∑ a : ZMod d, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => mul_nonneg (pow_nonneg hl0.le i) (hx.1 a i))
    _ ≤ ∑ a : ZMod d, D a := Finset.sum_le_sum fun a _ => flow_out_le hx a
end Formalism.IncomingBounds
