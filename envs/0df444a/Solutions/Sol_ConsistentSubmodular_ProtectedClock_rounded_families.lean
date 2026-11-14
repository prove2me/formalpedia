-- Prove2me | solution 1 for ConsistentSubmodular.ProtectedClock.rounded_families
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:33.604545+00:00
-- url     : https://prove2.me/submissions/6c665db2-1ead-436a-b75c-b9e36aedc86c

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ClockWindows
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundedWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProgramAssembly
import Theorems.Thm_ConsistentSubmodular_ProtectedClock_retained_tests_prefix

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

theorem windowBuffer_terminal (n i : ℕ) :
    C.windowBuffer n i (C.windowDuration i) = arrivedPrefix n (C.start (i + 1))\arrivedPrefix n (C.start i) := by
  simp [windowBuffer, windowOld, C.windowDuration_end]

variable {n : ℕ} (f : Objective n) (κ : ℕ)

/-- Every actual-time prefix competitor fits inside the old core plus new buffer. -/
theorem window_benchmark_dominates (i u : ℕ) :
    f.prefixOptimum κ (C.start i + u) ≤
      f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i u) κ :=
  f.optimum_le_windowOptimum (C.windowOld n i) (arrivedPrefix n (C.start i + u)) κ

theorem window_bridge_arrived (i : ℕ) :
    C.windowTerminal f κ i ∪ C.windowInitial f κ (i + 1) ⊆ arrivedPrefix n (C.start (i + 1)) := by
  apply Finset.union_subset
  · exact (C.windowTerminal_spec f κ i).1.trans (arrivedPrefix_mono (C.start_mono (Nat.le_succ i)))
  · exact (C.windowInitial_spec f κ (i + 1)).1

end ProtectedClock

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedClock
variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)
variable {n : ℕ} (f : Objective n) (κ : ℕ) (O : CertificateFamily) (N : ℕ) (hN : 200 ≤ N)
variable (HW LW HB LB B L : ℕ)

theorem solution
    (R : ∀ i, RoundedWindow (C.fractionalWindows f κ O N (by omega) i) HW LW)
    (hcardW : (κ : ℝ) + κ / N + HW ≤ B) (hcardB : (κ : ℝ) + κ / N + HB ≤ B)
    (hLW : LW ≤ L) (hLB : LB ≤ L)
    (bridges : ∀ i, ∃ P : SetOperationPath n,
      P.node 0 = C.windowTerminal f κ i ∧ P.node P.length = C.windowInitial f κ (i + 1) ∧
      P.length ≤ LB * κ ∧ ∀ j, P.node j ⊆ C.windowTerminal f κ i ∪ C.windowInitial f κ (i + 1) ∧
        ((P.node j).card : ℝ) ≤ κ + κ / N + HB ∧
        (O.level - 2 / N) * f.prefixOptimum κ (C.start (i + 1)) ≤
          f.value (C.windowBuffer n i (C.windowDuration i) ∪ P.node j)) :
    ∃ W : RoundedWindowFamily f κ (O.level - 2 * ((1 : ℝ) / N)) C B L,
      Nonempty (RoundedBridgeFamily W) := by
  have hN0 : 0 < N := by omega
  let W : RoundedWindowFamily f κ (O.level - 2 * ((1 : ℝ) / N)) C B L := {
    entry := fun i => (R i).entry
    exit := fun i => (R i).exit
    join := fun i => (R i).join
    initial_card := fun i => by rw [(R i).entry_initial]; exact (C.windowInitial_spec f κ i).2.1
    entry_card := fun i j => by exact_mod_cast ((R i).entry_card j).trans hcardW
    exit_card := fun i j => by exact_mod_cast ((R i).exit_card j).trans hcardW
    entry_arrived := fun i j => (R i).entry_subset j
    exit_arrived := fun i j => (R i).exit_subset j
    length := fun i => (R i).length.trans (Nat.mul_le_mul_right κ hLW)
    entry_value := fun i j => by
      have hh := (R i).entry_good j
      simpa only [C.windowBuffer_zero, Finset.empty_union, Objective.prefixOptimum,
        windowOld, mul_one_div] using hh
    exit_value := fun i j => by
      have hh := (R i).exit_good j
      have hb := C.window_benchmark_dominates f κ i (C.windowDuration i)
      rw [C.windowDuration_end] at hb
      have hg : (O.level - 2 / N) * f.prefixOptimum κ (C.start (i + 1)) ≤
          f.value (C.windowBuffer n i (C.windowDuration i) ∪ (R i).exit.node j) := by
        by_cases hβ : 0 ≤ O.level - 2 / N
        · exact (mul_le_mul_of_nonneg_left hb hβ).trans hh
        · have hp := f.prefixOptimum_nonnegative κ (C.start (i + 1))
          have hf := f.nonnegative (C.windowBuffer n i (C.windowDuration i) ∪ (R i).exit.node j)
          nlinarith
      simpa only [C.windowBuffer_terminal, Finset.union_comm, mul_one_div] using hg
    checkpoint_value := fun i t ht0 ht1 => by
      have hh := C.retained_tests_prefix f κ O N hN0 i ((R i).entry.node (R i).entry.length)
        ((R i).checkpoint_tests) t ht0 ht1
      simpa only [mul_one_div] using hh }
  let P := fun i => Classical.choose (bridges i)
  have hP i := Classical.choose_spec (bridges i)
  refine ⟨W, ⟨{
    path := P
    initial := ?_
    terminal := ?_
    cardinality := ?_
    arrived := ?_
    length := ?_
    value := ?_ }⟩⟩
  · intro i
    exact (hP i).1.trans (R i).exit_terminal.symm
  · intro i
    exact (hP i).2.1.trans (R (i + 1)).entry_initial.symm
  · intro i j
    exact_mod_cast ((hP i).2.2.2 j).2.1.trans hcardB
  · intro i j
    exact ((hP i).2.2.2 j).1.trans (C.window_bridge_arrived f κ i)
  · intro i
    exact (hP i).2.2.1.trans (Nat.mul_le_mul_right κ hLB)
  · intro i j
    have hh := ((hP i).2.2.2 j).2.2
    simpa only [P, C.windowBuffer_terminal, Finset.union_comm, mul_one_div] using hh

end
