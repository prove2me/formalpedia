-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_sparse_rightpayment_subtype_signed_absolute_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:37:55.796452+00:00
-- url     : https://prove2.me/submissions/a274998a-e8b5-4f40-a9ad-c18e625757f1

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
noncomputable section

/-- A right-payment correction vanishing off its actual positive-atom carrier inherits the subtype signed and absolute budget. -/
theorem solution
    {ι : Type*} (S : Set ι) (J : ι → ℝ) (B : ℝ)
    (hzero : ∀ i, i ∉ S → J i = 0)
    (hSummS : Summable (fun a : S => J a.val))
    (hNonposS : (∑' a : S, J a.val) ≤ 0)
    (hAbsS : Summable (fun a : S => |J a.val|))
    (hBoundS : (∑' a : S, |J a.val|) ≤ B) :
    Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
      Summable (fun i : ι => |J i|) ∧ (∑' i : ι, |J i|) ≤ B := by
  have hSupp : Function.support J ⊆ S := by
    intro i hi
    by_contra hn
    exact hi (hzero i hn)
  have hSuppAbs : Function.support (fun i : ι => |J i|) ⊆ S := by
    intro i hi
    by_contra hn
    exact hi (by simp [hzero i hn])
  have hInd : S.indicator J = J := by
    funext i
    by_cases hi : i ∈ S
    · simp [Set.indicator, hi]
    · simp [Set.indicator, hi, hzero i hi]
  have hIndAbs : S.indicator (fun i : ι => |J i|) = (fun i => |J i|) := by
    funext i
    by_cases hi : i ∈ S
    · simp [Set.indicator, hi]
    · simp [Set.indicator, hi, hzero i hi]
  have hSum : Summable J := by
    rw [← hInd]
    exact summable_subtype_iff_indicator.mp hSummS
  have hSumAbs : Summable (fun i : ι => |J i|) := by
    rw [← hIndAbs]
    exact summable_subtype_iff_indicator.mp hAbsS
  refine ⟨hSum, ?_, hSumAbs, ?_⟩
  · calc
      (∑' i : ι, J i) = (∑' a : S, J a.val) :=
        (tsum_subtype_eq_of_support_subset hSupp).symm
      _ ≤ 0 := hNonposS
  · calc
      (∑' i : ι, |J i|) = (∑' a : S, |J a.val|) :=
        (tsum_subtype_eq_of_support_subset hSuppAbs).symm
      _ ≤ B := hBoundS
