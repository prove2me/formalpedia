-- Prove2me | solution 1 for ConsistentSubmodular.ProtectedClock.window_bridge_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:43.713521+00:00
-- url     : https://prove2.me/submissions/5967c01b-913a-423c-8722-ba805f66cb3a

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ClockWindows

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

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

end Objective

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedClock

variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)

theorem separated (i : ℕ) : C.start i + ell ≤ C.start (i + 1) :=
  (C.upper i).trans (by simpa [Nat.add_assoc] using C.lower (i + 1))

theorem start_mono : Monotone C.start := by
  apply monotone_nat_of_le_succ
  intro i
  exact (Nat.le_add_right _ _).trans (C.separated i)

end ProtectedClock

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedClock

variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)

theorem windowDuration_end (i : ℕ) : C.start i + C.windowDuration i = C.start (i + 1) :=
  Nat.add_sub_of_le (C.start_mono (Nat.le_succ i))

variable {n : ℕ} (f : Objective n) (κ : ℕ)

/-- Every actual-time prefix competitor fits inside the old core plus new buffer. -/
theorem window_benchmark_dominates (i u : ℕ) :
    f.prefixOptimum κ (C.start i + u) ≤
      f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i u) κ :=
  f.optimum_le_windowOptimum (C.windowOld n i) (arrivedPrefix n (C.start i + u)) κ

end ProtectedClock

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedClock
variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)
variable {n : ℕ} (f : Objective n) (κ : ℕ)

theorem solution (i : ℕ) :
    let buffer := C.windowBuffer n i (C.windowDuration i)
    let V := f.prefixOptimum κ (C.start (i + 1))
    V ≤ f.value (buffer ∪ C.windowTerminal f κ i) ∧
    V ≤ f.value (buffer ∪ C.windowInitial f κ (i + 1)) ∧
    f.value (C.windowTerminal f κ i) ≤ V ∧
    f.value (C.windowInitial f κ (i + 1)) ≤ V := by
  dsimp only
  have ht := C.windowTerminal_spec f κ i
  have hi := C.windowInitial_spec f κ (i + 1)
  refine ⟨?_, ?_, ?_, hi.2.2.le⟩
  · rw [ht.2.2]
    have hh := C.window_benchmark_dominates f κ i (C.windowDuration i)
    rwa [C.windowDuration_end] at hh
  · rw [← hi.2.2]
    exact f.monotone _ _ Finset.subset_union_right
  · have hsub : C.windowTerminal f κ i ⊆ arrivedPrefix n (C.start (i + 1)) :=
      ht.1.trans (arrivedPrefix_mono (C.start_mono (Nat.le_succ i)))
    simpa only [Objective.prefixOptimum, Finset.empty_union] using
      f.le_bufferedOptimum (Q := ∅) hsub ht.2.1

end
