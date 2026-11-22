-- Prove2me | solution 1 for Bl.general_b_fact_second_last.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:49.328136+00:00
-- url     : https://prove2.me/submissions/086f9d6d-e138-432d-9725-c78c8ccc6d9b

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second_last
namespace Bl.general_b_fact_second_last
theorem _root_.solution :
  ∀ (B : Int) {S : Nat} (c : Fin S → Int),
  (∀ (m : Fin S), LT.lt.{0} (abs.{0} (c m)) B) →
    Eq.{1} (Finset.sum.{0, 0} Finset.univ.{0} fun (m : Fin S) ↦ HMul.hMul.{0, 0, 0} (c m) (HPow.hPow.{0, 0, 0} B m.val))
        0 →
      ∀ (m : Fin S), Eq.{1} (c m) 0 := by
  intro B S
  induction S with
  | zero => intro c _ _ m; exact m.elim0
  | succ n ih =>
    intro c hc hs m
    have hB : 0 < B := lt_of_le_of_lt (abs_nonneg _) (hc 0)
    rw [Fin.sum_univ_succ] at hs
    have h2 : ∑ i : Fin n, c i.succ * B ^ (i.succ).val = B * ∑ i : Fin n, c i.succ * B ^ i.val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [h2, Fin.val_zero, pow_zero, mul_one] at hs
    have hd : B ∣ c 0 := ⟨-(∑ i : Fin n, c i.succ * B ^ i.val), by rw [mul_neg]; linarith⟩
    have h0 : c 0 = 0 := Int.eq_zero_of_abs_lt_dvd hd (hc 0)
    rw [h0, zero_add] at hs
    have hT : ∑ i : Fin n, c i.succ * B ^ i.val = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact absurd h hB.ne'
      · exact h
    have ih' := ih (fun i => c i.succ) (fun i => hc _) hT
    exact Fin.cases h0 (fun i => ih' i) m
end Bl.general_b_fact_second_last
