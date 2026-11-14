-- Prove2me | solution 1 for ConsistentSubmodular.SharedThreshold.change_probability
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:34.656865+00:00
-- url     : https://prove2.me/submissions/135d690e-c9ba-4839-a08a-077e8ecbc0fc

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace SharedThreshold

variable {d : ℕ} {z : Fin d → ℝ} (T : SharedThreshold z)

theorem intersection_probability (s t : Fin d) :
    T.law.probability (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = min (z s) (z t) := by
  rcases le_total (z s) (z t) with hst | hts
  · have heq : (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = (fun ω => s ∈ T.active ω) := by
      funext ω
      exact propext ⟨And.left, fun hs => ⟨hs, T.ordered ω s t hst hs⟩⟩
    rw [heq, T.inclusion, min_eq_left hst]
  · have heq : (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = (fun ω => t ∈ T.active ω) := by
      funext ω
      exact propext ⟨And.right, fun ht => ⟨T.ordered ω t s hts ht, ht⟩⟩
    rw [heq, T.inclusion, min_eq_right hts]

end SharedThreshold

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.SharedThreshold
variable {d : ℕ} {z : Fin d → ℝ} (T : SharedThreshold z)

theorem solution (s t : Fin d) :
    T.law.probability (fun ω =>
      (s ∈ T.active ω ∧ t ∉ T.active ω) ∨ (t ∈ T.active ω ∧ s ∉ T.active ω)) = |z s - z t| := by
  classical
  have hid : T.law.probability (fun ω =>
      (s ∈ T.active ω ∧ t ∉ T.active ω) ∨ (t ∈ T.active ω ∧ s ∉ T.active ω)) =
      T.law.probability (fun ω => s ∈ T.active ω) + T.law.probability (fun ω => t ∈ T.active ω) -
        2 * T.law.probability (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) := by
    unfold FiniteLaw.probability
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only
    by_cases hs : s ∈ T.active ω <;> by_cases ht : t ∈ T.active ω <;> simp [hs, ht]
    ring
  rw [hid, T.inclusion, T.inclusion, T.intersection_probability]
  rcases le_total (z s) (z t) with hst | hts
  · rw [min_eq_left hst, abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  · rw [min_eq_right hts, abs_of_nonneg (sub_nonneg.mpr hts)]
    ring

end
