-- Prove2me | solution 1 for ConsistentSubmodular.BridgeGrid.forced_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:32.040373+00:00
-- url     : https://prove2.me/submissions/1957b6f0-eec9-4a98-85e6-00d4eabad84a

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_Objective_sum_removal_marginals_le
import Theorems.Thm_ConsistentSubmodular_Objective_exists_penalized_core

section

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem solution (f : Objective n) (U : Finset (Fin n)) (H : ℕ) (hH : 0 < H)
    (V : ℝ) (hV : 0 < V) (hU : f.value U ≤ 2 * V) :
    ∃ D ⊆ U, D.card ≤ H ∧ ∀ e ∈ U, e ∉ D →
      f.value (insert e D) - f.value D ≤ 2 * V / H := by
  obtain ⟨D, hDU, hins, hrem⟩ := f.exists_penalized_core U (2 * V / H)
  refine ⟨D, hDU, ?_, hins⟩
  have hs : (∑ _e ∈ D, 2 * V / (H : ℝ)) ≤ ∑ e ∈ D, (f.value D - f.value (D.erase e)) := by
    exact Finset.sum_le_sum (fun e he => (hrem e he).le)
  have hsum := f.sum_removal_marginals_le D
  have hv := (f.monotone _ _ hDU).trans hU
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hpos : (0 : ℝ) < 2 * V / H := by positivity
  have hcancel : (H : ℝ) * (2 * V / H) = 2 * V := by field_simp
  have hbound : (D.card : ℝ) * (2 * V / H) ≤ (H : ℝ) * (2 * V / H) := by
    rw [hcancel]
    linarith [f.nonnegative ∅]
  exact_mod_cast (mul_le_mul_iff_left₀ hpos).mp hbound

end
