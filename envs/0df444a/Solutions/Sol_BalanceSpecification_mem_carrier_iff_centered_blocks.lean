-- Prove2me | solution 1 for BalanceSpecification.mem_carrier_iff_centered_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:19.166091+00:00
-- url     : https://prove2.me/submissions/1c0f167e-fc0d-4d94-a7d0-30395feaecc1

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_exists_centered_block_realization
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_avoidingLanguage
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_languageShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {Y : ShiftSpace A} {x : Configuration A} :
    x ∈ Y.carrier ↔ ∀ n : ℕ, block x (-(n : ℤ)) (2 * n + 1) ∈ language Y := by
  constructor
  · intro hx n
    exact block_mem_language hx _ _
  · intro h
    apply Y.isClosed.closure_subset
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨s, V, hV, hsub⟩ := isOpen_pi_iff.mp hU x hxU
    classical
    let M : ℕ := ∑ i ∈ s, i.natAbs
    obtain ⟨y, hy, hblocks⟩ := exists_centered_block_realization (h M)
    have hagree : ∀ i ∈ s, y i = x i := by
      intro i hi
      have habs : i.natAbs ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
      have hu : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
      have hl : -i ≤ (i.natAbs : ℤ) := by
        simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -i))
      let j : ℕ := ((M : ℤ) + i).toNat
      have hjcast : (j : ℤ) = (M : ℤ) + i := Int.toNat_of_nonneg (by omega)
      have hj : j < 2 * M + 1 := by omega
      have he := List.getElem_of_eq hblocks
        (show j < (block y (-(M : ℤ)) (2 * M + 1)).length by
          simpa only [length_block] using hj)
      simp only [block, List.getElem_ofFn] at he
      simpa only [hjcast, neg_add_cancel_left] using he
    refine ⟨y, hsub ?_, hy⟩
    intro i hi
    rw [hagree i hi]
    exact (hV i hi).2
end BalanceSpecification
