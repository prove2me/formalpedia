-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_closure_avoids_second_collision
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T09:42:49.578098+00:00
-- url     : https://prove2.me/submissions/3ffd0345-fa84-4a3e-8516-c0b306ffc82d

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_left_component_second_collision_separated

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure (leftEnergyComponent μ c),
      0 < secondCollisionDistanceSq s := by
  obtain ⟨δ, hδ, hsep⟩ :=
    left_component_second_collision_separated μ c hμ0 hμ1 hc
  have hdcont : Continuous (fun t : Phase =>
      Real.sqrt (secondCollisionDistanceSq t)) := by
    dsimp [secondCollisionDistanceSq]
    fun_prop
  have hclosed : IsClosed {t : Phase |
      δ ≤ Real.sqrt (secondCollisionDistanceSq t)} :=
    isClosed_Ici.preimage hdcont
  have hsepclosure : closure (leftEnergyComponent μ c) ⊆
      {t : Phase | δ ≤ Real.sqrt (secondCollisionDistanceSq t)} :=
    hclosed.closure_subset_iff.mpr (by
      intro t ht
      exact hsep t ht)
  intro s hs
  have hsqrt : 0 < Real.sqrt (secondCollisionDistanceSq s) :=
    lt_of_lt_of_le hδ (hsepclosure hs)
  exact Real.sqrt_pos.mp hsqrt
