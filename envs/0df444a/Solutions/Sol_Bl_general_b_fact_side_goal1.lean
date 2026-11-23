-- Prove2me | solution 1 for Bl.general_b_fact_side.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:38.323462+00:00
-- url     : https://prove2.me/submissions/7f7e1642-1a2d-42f6-9b3d-3c3115c51e45

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSide_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_3 u_4
open Bl Bl.general_b_fact_side
namespace Bl.general_b_fact_side
theorem _root_.solution :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] [inst_1 : IsLocalRing.{u_1} R] [IsNoetherianRing.{u_1} R] {N₁ : Type u_3}
  {N₂ : Type u_4} [inst_3 : AddCommGroup.{u_3} N₁] [inst_4 : Module.{u_1, u_3} R N₁] [Module.Finite.{u_1, u_3} R N₁]
  [inst_6 : AddCommGroup.{u_4} N₂] [inst_7 : Module.{u_1, u_4} R N₂] [Module.Finite.{u_1, u_4} R N₂],
  Not (Membership.mem.{u_1, u_1} (associatedPrimes.{u_1, u_3} R N₁) (IsLocalRing.maximalIdeal.{u_1} R)) →
    Not (Membership.mem.{u_1, u_1} (associatedPrimes.{u_1, u_4} R N₂) (IsLocalRing.maximalIdeal.{u_1} R)) →
      Exists.{u_1 + 1} fun (z : R) ↦
        And (Membership.mem.{u_1, u_1} (IsLocalRing.maximalIdeal.{u_1} R) z)
          (And (IsSMulRegular.{u_1, u_3} N₁ z) (IsSMulRegular.{u_1, u_4} N₂ z)) := by
  intro R _ _ _ N₁ N₂ _ _ _ _ _ _ h1 h2
  have hfin : (associatedPrimes R N₁ ∪ associatedPrimes R N₂).Finite :=
    (associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)
  have hns : ¬ ((IsLocalRing.maximalIdeal R : Set R) ⊆
      ⋃ p ∈ associatedPrimes R N₁ ∪ associatedPrimes R N₂, (p : Set R)) := by
    intro hsub
    rw [Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite hfin ⊥ ⊥
      (fun I hI _ _ => hI.elim (fun h => h.1) (fun h => h.1)) bot_ne_top bot_ne_top] at hsub
    exact hsub.elim h1 h2
  obtain ⟨z, hzm, hz⟩ := Set.not_subset.mp hns
  refine ⟨z, hzm, ?_, ?_⟩
  · have hz1 : z ∉ ⋃ p ∈ associatedPrimes R N₁, (p : Set R) := fun h => by
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp h
      exact hz (Set.mem_biUnion (Or.inl hp) hzp)
    rw [biUnion_associatedPrimes_eq_compl_regular R N₁] at hz1
    simpa using hz1
  · have hz2 : z ∉ ⋃ p ∈ associatedPrimes R N₂, (p : Set R) := fun h => by
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp h
      exact hz (Set.mem_biUnion (Or.inr hp) hzp)
    rw [biUnion_associatedPrimes_eq_compl_regular R N₂] at hz2
    simpa using hz2
end Bl.general_b_fact_side
