-- Prove2me | solution 1 for GIGnBounds.Tail.corollary_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:10:53.561716+00:00
-- url     : https://prove2.me/submissions/7ca44780-b331-4f46-8bc5-f2c1a67a2049
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting
import Theorems.Thm_GIGnBounds_Tail_lemma_7

open MeasureTheory ProbabilityTheory GIGnBounds.Tail

theorem solution (n : ℕ) (hn : 0 < n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hS1 : mean μS = 1) (hstab : rate μA < n * rate μS)
    (π : Measure ℕ) (hπ : IsSteadyStateLaw n μA μS π)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P (n - ⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊) μA μS) :
    π.real {q : ℕ | n ≤ q} ≤
      P.real {ω | ((⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ : ℝ) : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} := by
  have hμ : 0 < rate μA := inv_pos.mpr hA.mean_pos
  have hrateS : rate μS = 1 := by rw [rate, hS1]; norm_num
  have hstab' : rate μA < n := by rw [hrateS, mul_one] at hstab; exact hstab
  have hfle : (⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ : ℝ) ≤ (1 / 2 : ℝ) * (n - rate μA) := by
    exact Nat.floor_le (by nlinarith [hstab'])
  have hfn : ⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ < n := by
    have : (⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ : ℝ) < n := by linarith [hstab']
    exact_mod_cast this
  have hn'1 : 1 ≤ n - ⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ := by omega
  have hn'2 : n - ⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ ≤ n := Nat.sub_le n _
  have hcast : ((n - ⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ : ℕ) : ℝ) = (n : ℝ) - (⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ : ℝ) := Nat.cast_sub hfn.le
  have h7 := GIGnBounds.Tail.lemma_7 n hn μA μS hA hS hstab
    π hπ (n - ⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊) hn'1 hn'2 0 (by rw [hcast]; simp) Ω P F
  have hset : {q : ℕ | n ≤ q} = {q : ℕ | (0 : ℝ) ≤ (q : ℝ) - n} := by
    ext q
    simp only [Set.mem_setOf_eq, sub_nonneg, Nat.cast_le]
  rw [hset]
  have hthr : ((0 + ((n : ℝ) - ((n - ⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ : ℕ) : ℝ)) : ℝ) : EReal) = ((⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ : ℝ) : EReal) := by
    rw [hcast]; congr 1; ring
  rw [hthr] at h7
  exact h7
