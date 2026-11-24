-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.sum_wt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:48.179117+00:00
-- url     : https://prove2.me/submissions/1d1d29c6-fec2-4014-9bd1-846e4754ea25

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_wt_nonneg
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_wt_le_one
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_wt_tail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (R : ℝ) (hR : 1 ≤ R) (T : Finset ℕ) : ∑ m ∈ T, wt R m ≤ 9 * R := by
  obtain ⟨N, hN, hN'⟩ : ∃ N : ℕ, 2 * R ≤ (N : ℝ) ∧ (N : ℝ) < 2 * R + 1 :=
    ⟨⌈2 * R⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩
  obtain ⟨J, hsub⟩ : ∃ J : ℕ, T ⊆ Finset.range (N + 2 + J) := by
    refine ⟨T.sup id + 1, fun m hm => ?_⟩
    have hm' : m ≤ T.sup id := Finset.le_sup (f := id) hm
    rw [Finset.mem_range]
    omega
  have h1 : ∑ m ∈ T, wt R m ≤ ∑ m ∈ Finset.range (N + 2 + J), wt R m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => wt_nonneg R m)
  rw [Finset.sum_range_add] at h1
  have h2 : ∑ m ∈ Finset.range (N + 2), wt R m ≤ (N : ℝ) + 2 := by
    calc ∑ m ∈ Finset.range (N + 2), wt R m ≤ ∑ m ∈ Finset.range (N + 2), (1 : ℝ) :=
          Finset.sum_le_sum (fun m _ => wt_le_one R m)
      _ = (N : ℝ) + 2 := by simp
  have hc : 0 < 2 * R := by linarith
  have hsc : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr hc
  have hC : 0 ≤ 2 * (2 * R) * Real.sqrt (2 * R) := (mul_pos (mul_pos two_pos hc) hsc).le
  have h3 : ∑ j ∈ Finset.range J, wt R (N + 2 + j) ≤ 4 * R := by
    calc ∑ j ∈ Finset.range J, wt R (N + 2 + j)
        ≤ ∑ j ∈ Finset.range J, 2 * (2 * R) * Real.sqrt (2 * R) *
            (1 / Real.sqrt ((N : ℝ) + (j : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((j + 1 : ℕ) : ℝ))) :=
          Finset.sum_le_sum (fun j _ => wt_tail R hR N hN j)
      _ = 2 * (2 * R) * Real.sqrt (2 * R) *
            (1 / Real.sqrt ((N : ℝ) + ((0 : ℕ) : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((J : ℕ) : ℝ))) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_range_sub' (fun j : ℕ => 1 / Real.sqrt ((N : ℝ) + (j : ℝ))) J
      _ ≤ 2 * (2 * R) * Real.sqrt (2 * R) * (1 / Real.sqrt (2 * R)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          have e0 : (N : ℝ) + ((0 : ℕ) : ℝ) = N := by simp
          rw [e0]
          have ha := one_div_le_one_div_of_le hsc (Real.sqrt_le_sqrt hN)
          have hb : 0 ≤ 1 / Real.sqrt ((N : ℝ) + ((J : ℕ) : ℝ)) := by positivity
          linarith
      _ = 4 * R := by
          rw [mul_one_div, mul_div_assoc, div_self hsc.ne', mul_one]; ring
  linarith
end Formalism.MainNotions.WeightedLatticeSum
