-- Prove2me | solution 1 for BirkhoffGlobalSection.first_ray_zero_in_left_negative_closure
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T12:33:24.136698+00:00
-- url     : https://prove2.me/submissions/80a9c9fe-d202-4ff5-861c-99d1f6bcfce0

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (x : Phase) (r : ℝ) (hr : 0 < r)
    (hnegative : ∀ t : ℝ, 0 ≤ t → t < r →
      leviCivitaHamiltonian μ c (fun i : Fin 4 => t * x i) < 0)
    (hfree : ∀ t : ℝ, 0 ≤ t → t ≤ r →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => t * x i)) :
    (fun i : Fin 4 => r * x i) ∈ closure
      (connectedComponentIn
        {s : Phase | leviCivitaHamiltonian μ c s < 0 ∧
          0 < secondCollisionDistanceSq s}
        (fun _ : Fin 4 => (0 : ℝ))) := by
  let f : ℝ → Phase := fun t i => t * x i
  let N : Set Phase :=
    {s | leviCivitaHamiltonian μ c s < 0 ∧ 0 < secondCollisionDistanceSq s}
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hf0 : f 0 = (fun _ : Fin 4 => (0 : ℝ)) := by
    funext i
    simp [f]
  have himage : f '' Set.Ico 0 r ⊆ connectedComponentIn N (fun _ => 0) := by
    apply (isPreconnected_Ico.image f hf.continuousOn).subset_connectedComponentIn
      (by
        rw [← hf0]
        exact Set.mem_image_of_mem f ⟨le_refl 0, hr⟩)
    rintro s ⟨t, ⟨ht0, htr⟩, rfl⟩
    exact ⟨hnegative t ht0 htr, hfree t ht0 htr.le⟩
  have hrclosure : r ∈ closure (Set.Ico (0 : ℝ) r) := by
    rw [closure_Ico (ne_of_lt hr)]
    exact ⟨hr.le, le_refl r⟩
  exact closure_mono himage (mem_closure_image hf.continuousAt hrclosure)
