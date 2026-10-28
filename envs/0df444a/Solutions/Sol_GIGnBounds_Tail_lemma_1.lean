-- Prove2me | solution 1 for GIGnBounds.Tail.lemma_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:10:52.912415+00:00
-- url     : https://prove2.me/submissions/cf99aef1-f374-4b45-8310-34806c425bdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting
import Theorems.Thm_GIGnBounds_Tail_lemma_7

open MeasureTheory ProbabilityTheory GIGnBounds.Tail

theorem solution (n : ℕ) (hn : 0 < n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hstab : rate μA < n * rate μS)
    (π : Measure ℕ) (hπ : IsSteadyStateLaw n μA μS π)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n μA μS) (x : ℝ) (hx : 0 < x) :
    π.real {q : ℕ | x ≤ ((q - n : ℕ) : ℝ)} ≤
      P.real {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} := by
  have h7 := GIGnBounds.Tail.lemma_7 n hn μA μS hA hS hstab π hπ n hn le_rfl x
    (by simp; linarith) Ω P F
  have hset : {q : ℕ | x ≤ ((q - n : ℕ) : ℝ)} = {q : ℕ | x ≤ (q : ℝ) - n} := by
    ext q
    simp only [Set.mem_setOf_eq]
    rcases le_total n q with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h]
      have : (q : ℝ) ≤ n := by exact_mod_cast h
      constructor <;> intro h' <;> push_cast at h' ⊢ <;> linarith
  rw [hset]
  simpa using h7
