-- Prove2me | solution 1 for BalanceSpecification.exists_centered_cylinder_subset_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:47.271517+00:00
-- url     : https://prove2.me/submissions/0113118c-7be7-491e-a69a-eb762ea24b62

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
open Set TopologicalSpace
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    {U : Set X.carrier} (hU : IsOpen U) {x : X.carrier} (hx : x ∈ U) :
    ∃ N : ℕ, ∃ w : Word A,
      w ∈ language X ∧ w.length = 2*N+1 ∧
      x ∈ cylinder X w (-(N : ℤ)) ∧ cylinder X w (-(N : ℤ)) ⊆ U := by
  classical
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨V, ⟨S, F, _hS, rfl⟩, hxV, hVO⟩ :=
    (isTopologicalBasis_pi fun _ : ℤ => isTopologicalBasis_opens).exists_subset_of_mem_open hx hO
  let N := ∑ i ∈ F, i.natAbs
  let w := block x.val (-(N : ℤ)) (2*N+1)
  refine ⟨N, w, block_mem_language x.property _ _, length_block _ _ _, ?_, ?_⟩
  · change block x.val (-(N : ℤ)) w.length = w
    simp only [w, length_block]
  · intro y hy
    apply hVO
    intro i hi
    have habs : i.natAbs ≤ N := Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) hi
    have hupper : i ≤ ((i.natAbs : ℕ) : ℤ) := Int.le_natAbs
    have hlower : -i ≤ ((i.natAbs : ℕ) : ℤ) := by
      simpa only [Int.natAbs_neg] using Int.le_natAbs (a := -i)
    let j := (i + (N : ℤ)).toNat
    have hjcast : (j : ℤ) = i + (N : ℤ) := Int.toNat_of_nonneg (by omega)
    have hj : j < 2*N+1 := by omega
    have hblocks : block y.val (-(N : ℤ)) (2*N+1) =
        block x.val (-(N : ℤ)) (2*N+1) := by
      change block y.val (-(N : ℤ)) w.length = w at hy
      simpa only [w, length_block] using hy
    have he := List.getElem_of_eq hblocks
      (show j < (block y.val (-(N : ℤ)) (2*N+1)).length by
        simpa only [length_block] using hj)
    simp only [block, List.getElem_ofFn] at he
    have hindex : -(N : ℤ) + (j : ℤ) = i := by omega
    have hcoord : y.val i = x.val i := by simpa only [hindex] using he
    rw [hcoord]
    exact hxV i hi
end BalanceSpecification
