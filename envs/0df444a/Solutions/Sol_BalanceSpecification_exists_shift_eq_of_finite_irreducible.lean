-- Prove2me | solution 1 for BalanceSpecification.exists_shift_eq_of_finite_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:12.562845+00:00
-- url     : https://prove2.me/submissions/c4f7081d-2a49-4655-9dbe-6965184294a0

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_exists_injective_centered_block
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_block_shift
public import Theorems.Thm_BalanceSpecification_block_subword
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
omit [Fintype A]
namespace BalanceSpecification
theorem _root_.solution (hfin : X.carrier.Finite)
    (hirr : Irreducible X) {x y : Configuration A}
    (hx : x ∈ X.carrier) (hy : y ∈ X.carrier) :
    ∃ n : ℕ, SymbolicDynamics.FullShift.shift (n : ℤ) x = y := by
  classical
  obtain ⟨M, hM⟩ := exists_injective_centered_block hfin.toFinset
  let N := 2 * M + 1
  let u := block x (-(M : ℤ)) N
  let v := block y (-(M : ℤ)) N
  have hu : u ∈ language X := block_mem_language hx _ _
  have hv : v ∈ language X := block_mem_language hy _ _
  obtain ⟨w, hw, huwv⟩ := hirr u hu v hv
  obtain ⟨z, hz, hzblock⟩ := mem_language_iff_exists_block_zero.mp huwv
  have hfirst : block z 0 u.length = u := by
    apply block_subword z 0 [] u (w ++ v)
    simpa only [List.nil_append, List.append_assoc] using hzblock
  have hlast : block z (u.length + w.length) v.length = v := by
    have hh := block_subword z 0 (u ++ w) v []
      (by simpa only [List.append_nil] using hzblock)
    simpa only [zero_add, List.length_append, Nat.cast_add] using hh
  have ha : SymbolicDynamics.FullShift.shift (M : ℤ) z = x := by
    apply hM (hfin.mem_toFinset.mpr (X.mapsTo (M : ℤ) hz)) (hfin.mem_toFinset.mpr hx)
    change block (SymbolicDynamics.FullShift.shift (M : ℤ) z) (-(M : ℤ)) N = u
    rw [block_shift, add_neg_cancel]
    simpa only [u, length_block] using hfirst
  have hb : SymbolicDynamics.FullShift.shift ((M : ℤ) + u.length + w.length) z = y := by
    apply hM (hfin.mem_toFinset.mpr (X.mapsTo _ hz)) (hfin.mem_toFinset.mpr hy)
    change block (SymbolicDynamics.FullShift.shift ((M : ℤ) + u.length + w.length) z)
      (-(M : ℤ)) N = v
    rw [block_shift]
    have hstart : ((M : ℤ) + u.length + w.length) + -(M : ℤ) = u.length + w.length := by omega
    rw [hstart]
    simpa only [v, length_block] using hlast
  refine ⟨u.length + w.length, ?_⟩
  rw [← ha]
  have hcomp : SymbolicDynamics.FullShift.shift ((u.length + w.length : ℕ) : ℤ)
      (SymbolicDynamics.FullShift.shift (M : ℤ) z) =
      SymbolicDynamics.FullShift.shift ((M : ℤ) + u.length + w.length) z := by
    funext i
    simp only [SymbolicDynamics.FullShift.shift_apply, Nat.cast_add, add_assoc]
  exact hcomp.trans hb
end BalanceSpecification
