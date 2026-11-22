-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.commGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:32.290824+00:00
-- url     : https://prove2.me/submissions/ce71feba-6db9-4e24-b62c-3622eb09238e

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Groups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open scoped commutatorElement
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : CommGen := by
  intro H _ g hgen hcen h01
  set C := Subgroup.closure
    ({⁅g 0, g 2⁆, ⁅g 0, g 3⁆, ⁅g 1, g 2⁆, ⁅g 1, g 3⁆, ⁅g 2, g 3⁆} : Set H) with hCdef
  have h01' : ⁅g 0, g 1⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h01
  have h10' : ⁅g 1, g 0⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h01.symm
  have hbase : ∀ i j : Fin 4, ⁅g i, g j⁆ ∈ C := by
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp only <;>
      first
      | (rw [commutatorElement_self]; exact C.one_mem)
      | (simp [h01', h10']; done)
      | (apply Subgroup.subset_closure; simp; done)
      | (rw [← commutatorElement_inv]; apply C.inv_mem; apply Subgroup.subset_closure; simp; done)
  have hall : ∀ x y : H, ⁅x, y⁆ ∈ C := by
    have h1 : ∀ (i : Fin 4) (y : H), ⁅y, g i⁆ ∈ C := by
      intro i y
      have hle : Subgroup.closure (Set.range g) ≤ commLeftSub hcen C (g i) := by
        rw [Subgroup.closure_le]; rintro _ ⟨j, rfl⟩; exact hbase j i
      exact hle (hgen ▸ Subgroup.mem_top y)
    intro x y
    have hle : Subgroup.closure (Set.range g) ≤ commLeftSub hcen C y := by
      rw [Subgroup.closure_le]; rintro _ ⟨i, rfl⟩
      show ⁅g i, y⁆ ∈ C
      rw [← commutatorElement_inv]; exact C.inv_mem (h1 i y)
    exact hle (hgen ▸ Subgroup.mem_top x)
  have heq : commutator H = C := by
    apply le_antisymm
    · rw [commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨x, y, rfl⟩; exact hall x y
    · rw [hCdef, Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;>
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine ⟨heq, ?_⟩
  intro hsq
  let c : Fin 5 → H := ![⁅g 0, g 2⁆, ⁅g 0, g 3⁆, ⁅g 1, g 2⁆, ⁅g 1, g 3⁆, ⁅g 2, g 3⁆]
  have hcmem : ∀ i, c i ∈ commutator H := by
    intro i; rw [heq, hCdef]; apply Subgroup.subset_closure
    fin_cases i <;> simp [c]
  have hcomm : Pairwise fun i j : Fin 5 => ∀ x y : H, x ∈ Subgroup.zpowers (c i) →
      y ∈ Subgroup.zpowers (c j) → Commute x y := by
    intro i j _ x y hx _
    have hxc : x ∈ Subgroup.center H := (Subgroup.zpowers_le.mpr (hcen (hcmem i))) hx
    exact (Subgroup.mem_center_iff.mp hxc y).symm
  let φ := Subgroup.noncommPiCoprod hcomm
  have hfin : ∀ i, Nat.card (Subgroup.zpowers (c i)) ≤ 2 := by
    intro i; rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one (by norm_num) (hsq _ (hcmem i))
  have : ∀ i, Finite (Subgroup.zpowers (c i)) := fun i => Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, by norm_num, hsq _ (hcmem i)⟩)).ne')
  have hle : C ≤ φ.range := by
    rw [hCdef, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hi : ∃ i, c i = z := by
      rcases hz with rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
    obtain ⟨i, rfl⟩ := hi
    exact ⟨Pi.mulSingle i ⟨c i, Subgroup.mem_zpowers _⟩, by simp [φ]⟩
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  calc Nat.card (commutator H) = Nat.card C := by rw [heq]
    _ ≤ Nat.card φ.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (∀ i, Subgroup.zpowers (c i)) :=
        Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
    _ = ∏ i, Nat.card (Subgroup.zpowers (c i)) := Nat.card_pi
    _ ≤ ∏ _i : Fin 5, 2 := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hfin i)
    _ = 2 ^ 5 := by simp
end Formalism.TwoAdicCyclotomicDecomposition
