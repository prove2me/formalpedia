-- Prove2me | solution 1 for ConsistentSubmodular.Objective.unstable_transition_buffer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:09.418183+00:00
-- url     : https://prove2.me/submissions/5d5f7e59-3d90-42a3-9590-13fa97531cdb

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProtectedClock

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

theorem protected_buffer_subset {s t width : ℕ} (hst : s ≤ t)
    (hage : t - s ≤ width) :
    arrivedPrefix n t \ arrivedPrefix n s ⊆ rollingBuffer n width t := by
  intro e he
  simp only [Finset.mem_sdiff, mem_arrivedPrefix] at he
  simp only [rollingBuffer, Finset.mem_sdiff, mem_arrivedPrefix]
  omega

namespace Objective

variable (f : Objective n)

/-- Every competitor's new part is already in the window buffer. -/
theorem value_le_windowOptimum {N E A : Finset (Fin n)} {k : ℕ}
    (hAE : A ⊆ E) (hAk : A.card ≤ k) :
    f.value A ≤ f.bufferedOptimum N (E \ N) k := by
  have hsub : A ⊆ (E \ N) ∪ (A ∩ N) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    by_cases heN : e ∈ N
    · exact Or.inr ⟨he, heN⟩
    · exact Or.inl ⟨hAE he, heN⟩
  exact (f.monotone A _ hsub).trans
    (f.le_bufferedOptimum Finset.inter_subset_right
      ((Finset.card_le_card Finset.inter_subset_left).trans hAk))

theorem optimum_le_windowOptimum (N E : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimum E ∅ k ≤ f.bufferedOptimum N (E \ N) k := by
  have hA := f.bufferedOptimizer_spec E ∅ k
  simpa [bufferedOptimum] using f.value_le_windowOptimum hA.1 hA.2.1

/-- The new arrivals cover the gain in the optimum. -/
theorem new_buffer_value_ge_gain (N E : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimum E ∅ k - f.bufferedOptimum N ∅ k ≤ f.value (E \ N) := by
  have hwin := f.optimum_le_windowOptimum N E k
  have hu := f.bufferedOptimum_le N (E \ N) k
  have h0 := f.nonnegative ∅
  linarith

/-- An interval whose optimum has grown by a factor of four is protected
entirely by the new arrivals. This includes zero initial optimum. -/
theorem unstable_buffer_protection (N E : Finset (Fin n)) (k : ℕ)
    (hgrowth : 4 * f.bufferedOptimum N ∅ k ≤ f.bufferedOptimum E ∅ k) :
    (3 : ℝ) / 4 * f.bufferedOptimum E ∅ k ≤ f.value (E \ N) := by
  have h := f.new_buffer_value_ge_gain N E k
  linarith

end Objective

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (k : ℕ) {η : ℝ} {b ell : ℕ}
    (C : ProtectedClock (f.prefixOptimum k) η b ell) (i t : ℕ)
    (ht0 : C.start i ≤ t) (ht1 : t ≤ C.start i + ell)
    (hu : 4 * f.prefixOptimum k ((i + 1) * b) ≤ f.prefixOptimum k (C.start i)) :
    (3 : ℝ) / 4 * f.prefixOptimum k t ≤ f.value (rollingBuffer n (4 * b) t) := by
  have hlow := C.lower i
  have hhigh := C.upper i
  have hg := hu.trans (f.prefixOptimum_monotone k ht0)
  have hp := f.unstable_buffer_protection (arrivedPrefix n ((i + 1) * b))
    (arrivedPrefix n t) k hg
  have hage : t - ((i + 1) * b) ≤ 4 * b := by
    have hh : t ≤ (i + 1) * b + b := by nlinarith
    omega
  have hsub := protected_buffer_subset (n := n) (s := (i + 1) * b) (t := t)
    (width := 4 * b) (by omega) hage
  exact hp.trans (f.monotone _ _ hsub)

end
