-- Prove2me | solution 1 for BrinSquier.metabelian_or_zsq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T08:17:51.249391+00:00
-- url     : https://prove2.me/submissions/f7080f4f-f0a9-4fc3-b19f-b9a377ed0a60

import Theorems.Thm_BrinSquier_zsq_of_not_abelian
import Theorems.Thm_BrinSquier_slope_one_commutator
import Theorems.Thm_BrinSquier_isPLF_mul
import Theorems.Thm_BrinSquier_isPLF_inv
import Theorems.Thm_BrinSquier_isPLFSlopeOne_mul
import Theorems.Thm_BrinSquier_isPLFSlopeOne_inv
import Definitions.Def_BrinSquier
import Mathlib

open scoped commutatorElement
open BrinSquier

namespace BS_33

/-- The slope-one piecewise-linear maps, as a subgroup: this is what the two closure
milestones buy. -/
def PLFSO : Subgroup (ℝ ≃o ℝ) where
  carrier := {x | IsPLFSlopeOne x}
  one_mem' := ⟨⟨∅, fun x _ => ⟨1, one_pos, 1, 0, fun y _ => by simp⟩⟩,
    ⟨0, 0, fun y _ => by simp⟩, ⟨0, 0, fun y _ => by simp⟩⟩
  mul_mem' := fun ha hb => isPLFSlopeOne_mul ha hb
  inv_mem' := fun ha => isPLFSlopeOne_inv ha

end BS_33

open BS_33 in
theorem solution (G : Subgroup (ℝ ≃o ℝ)) (hG : ∀ f ∈ G, IsPLF f) :
    (∀ u ∈ ⁅G, G⁆, ∀ v ∈ ⁅G, G⁆, u * v = v * u) ∨
      ∃ u ∈ G, ∃ v ∈ G, u * v = v * u ∧
        Function.Injective (fun p : ℤ × ℤ => u ^ p.1 * v ^ p.2) := by
  by_cases habel : ∀ u ∈ ⁅G, G⁆, ∀ v ∈ ⁅G, G⁆, u * v = v * u
  · exact Or.inl habel
  refine Or.inr ?_
  -- the derived subgroup lies inside `G`
  have hGG : ⁅G, G⁆ ≤ G := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)
  -- and lands in `PLFSO`: (2.14a) gives the slopes, the closure milestones the rest
  have hH : ∀ u ∈ ⁅G, G⁆, IsPLFSlopeOne u := by
    have hle : ⁅G, G⁆ ≤ PLFSO := by
      rw [Subgroup.commutator_le]
      intro p hp q hq
      rw [commutatorElement_def]
      exact ⟨isPLF_mul (isPLF_mul (isPLF_mul (hG p hp) (hG q hq)) (isPLF_inv (hG p hp)))
          (isPLF_inv (hG q hq)),
        (slope_one_commutator (hG p hp) (hG q hq)).1,
        (slope_one_commutator (hG p hp) (hG q hq)).2⟩
    exact fun u hu => hle hu
  obtain ⟨u, hu, v, hv, hcomm, hinj⟩ := BrinSquier.zsq_of_not_abelian ⁅G, G⁆ hH habel
  exact ⟨u, hGG hu, v, hGG hv, hcomm, hinj⟩
