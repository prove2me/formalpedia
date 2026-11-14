-- Prove2me | solution 1 for ConsistentSubmodular.ProtectedPrograms.arrived_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:44.301462+00:00
-- url     : https://prove2.me/submissions/32a1d38b-ca3a-43f2-b8df-426111b005e6

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule

section

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedClock

variable {n b ell R : ℕ} {F : ℕ → ℝ} {η : ℝ}

variable (C : ProtectedClock F η b ell)

theorem coreBlocks_before_first (P : ℕ → SetOperationPath n) (hinitial hjoin hlen)
    (t : ℕ) (ht : t / b = 0) :
    (C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory t = ∅ := by
  simp [BlockSchedule.trajectory, coreBlocks, ht]

theorem coreBlocks_in_block (P : ℕ → SetOperationPath n) (hinitial hjoin hlen)
    (i t : ℕ) (ht : t / b = i + 1) :
    (C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory t =
      (P i).node (R * (t - C.start i)) := by
  have htval := Nat.mod_add_div t b
  rw [ht] at htval
  have hl := C.lower i
  have heq : t % b - C.delay i = t - C.start i := by
    dsimp [delay]
    have hh : t % b + (i + 1) * b = t := by nlinarith
    omega
  simp [BlockSchedule.trajectory, coreBlocks, ht, heq]

end ProtectedClock

end ConsistentSubmodular

end

end

section

namespace ConsistentSubmodular

variable {n : ℕ}

theorem rollingBuffer_subset (width t : ℕ) : rollingBuffer n width t ⊆ arrivedPrefix n t :=
  Finset.sdiff_subset

end ConsistentSubmodular

end

section

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedPrograms

variable {n b ell κ R B : ℕ} {f : Objective n} {β η : ℝ} {F : ℕ → ℝ}

variable {C : ProtectedClock F η b ell} (P : ProtectedPrograms f κ β C R B)

theorem core_in_block (i t : ℕ) (ht : t / b = i + 1) :
    P.core t = (P.path i).node (R * (t - C.start i)) :=
  C.coreBlocks_in_block _ _ _ _ i t ht

end ProtectedPrograms

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedPrograms
variable {n b ell κ R B : ℕ} {f : Objective n} {β η : ℝ} {F : ℕ → ℝ}
variable {C : ProtectedClock F η b ell} (P : ProtectedPrograms f κ β C R B)

theorem solution (t : ℕ) : P.selected t ⊆ arrivedPrefix n t := by
  apply Finset.union_subset
  · cases hdiv : t / b with
    | zero => rw [core, C.coreBlocks_before_first _ _ _ _ t hdiv]; exact Finset.empty_subset _
    | succ i =>
      rw [P.core_in_block i t hdiv]
      by_cases ht : C.start i ≤ t
      · exact (P.arrived _ _).trans (arrivedPrefix_mono ht)
      · have he : t - C.start i = 0 := by omega
        rw [he, Nat.mul_zero]
        cases i with
        | zero => rw [P.initial]; exact Finset.empty_subset _
        | succ i =>
          rw [← P.joins i]
          have hu := C.upper i
          have hbnd := Nat.div_mul_le_self t b
          rw [hdiv] at hbnd
          have ha : C.start i ≤ t := (Nat.le_add_right _ _).trans
            (hu.trans (by simpa only [Nat.add_assoc] using hbnd))
          exact (P.arrived _ _).trans (arrivedPrefix_mono ha)
  · exact rollingBuffer_subset _ _

end
