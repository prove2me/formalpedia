-- Prove2me | solution 1 for ConsistentSubmodular.Chains.right_le_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:35.568215+00:00
-- url     : https://prove2.me/submissions/90791111-dd7f-4c7d-9874-0890d4da0a58

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

section Consecutive

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)

include hI

theorem left_monotone : Monotone I.left := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  rw [hI.2.1 i]
  exact I.left_le_right i.castSucc

end Consecutive

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
include hI

theorem solution {i j : Fin (N + 1)} (hij : i < j) : I.right i ≤ I.left j := by
  have hiN : i.val < N := by
    have := j.isLt
    rw [Fin.lt_def] at hij
    omega
  have hi : (⟨i.val, hiN⟩ : Fin N).castSucc = i := Fin.ext rfl
  rw [← hi, ← hI.2.1 ⟨i.val, hiN⟩]
  apply left_monotone hI
  rw [Fin.le_iff_val_le_val]
  rw [Fin.lt_def] at hij
  simp only [Fin.val_succ]
  omega

end
