-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a318_compact_HJB_finite_combined_positive_two_stream_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:04:02.032436+00:00
-- url     : https://prove2.me/submissions/55945ad1-68eb-4b57-9e76-7fcd96b03ec7

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a302_nonnegative_exponential_HJB_endpoint_upper_via_compact_start
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (f r z y : ℕ → ℝ) (θ K M B : ℝ)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hCell : ∀ i ∈ S, A i →
      max (f i) 0 ≤ K*Real.exp (θ*(y i+r i)) +
        M*(1+|r i|+z i^2/2))
    (hReserve : ∀ i ∈ S, A i → y i ≤ B) :
    max (∑ i ∈ S, if A i then f i else 0) 0 ≤
      (K*Real.exp (θ*B))*
        (∑ i ∈ S, if A i then Real.exp (θ*r i) else 0) +
      M*(∑ i ∈ S, if A i then 1+|r i|+z i^2/2 else 0) := by
  classical
  let U : ℕ → ℝ := fun i =>
    (K*Real.exp (θ*B))*Real.exp (θ*r i)
  let V : ℕ → ℝ := fun i =>
    M*(1+|r i|+z i^2/2)
  have hTerm (i : ℕ) (hi : i ∈ S) (ha : A i) :
      max (f i) 0 ≤ U i+V i := by
    have he := avram_ga_a302_nonnegative_exponential_HJB_endpoint_upper_via_compact_start
      θ K B (y i) (r i) hθ hK (hReserve i hi ha)
    calc
      max (f i) 0 ≤ K*Real.exp (θ*(y i+r i))+
        M*(1+|r i|+z i^2/2) := hCell i hi ha
      _ ≤ U i+V i := by
        dsimp [U,V]
        nlinarith [he]
  have hFirst :
      max (∑ i ∈ S, if A i then f i else 0) 0 ≤
        ∑ i ∈ S, if A i then max (f i) 0 else 0 := by
    apply max_le
    · apply Finset.sum_le_sum
      intro i hi
      by_cases ha : A i
      · simpa only [if_pos ha] using le_max_left (f i) 0
      · simp [ha]
    · apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity
  calc
    max (∑ i ∈ S, if A i then f i else 0) 0 ≤
      ∑ i ∈ S, if A i then max (f i) 0 else 0 := hFirst
    _ ≤ ∑ i ∈ S, (if A i then U i+V i else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases ha : A i
      · simpa only [if_pos ha] using hTerm i hi ha
      · simp [ha]
    _ = (K*Real.exp (θ*B))*
          (∑ i ∈ S, if A i then Real.exp (θ*r i) else 0) +
        M*(∑ i ∈ S, if A i then 1+|r i|+z i^2/2 else 0) := by
      have hTermEq (i : ℕ) :
          (if A i then U i+V i else 0) =
          (if A i then U i else 0)+(if A i then V i else 0) := by
        by_cases ha : A i <;> simp [ha]
      simp_rw [hTermEq]
      rw [Finset.sum_add_distrib]
      simp [U,V,Finset.mul_sum,mul_ite]
