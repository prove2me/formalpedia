-- Prove2me | solution 1 for BalanceSpecification.entropy_productShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:01.955215+00:00
-- url     : https://prove2.me/submissions/a20f3110-0fd0-49e0-81ef-8ff2fd2e6a1f

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_wordCount_productShift
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_tendsto_entropy
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty
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
open Filter
open scoped Topology
variable {A B : Type*}
namespace BalanceSpecification
theorem _root_.solution [Fintype A] [Fintype B]
    [TopologicalSpace A] [TopologicalSpace B] {X : ShiftSpace A} {Y : ShiftSpace B}
    (hX : X.carrier.Nonempty) (hY : Y.carrier.Nonempty) :
    entropy (productShift X Y) (productShift_nonempty hX hY) = entropy X hX + entropy Y hY := by
  have hlog (n : ℕ) :
      Real.log (wordCount (language (productShift X Y)) n) / n =
        Real.log (wordCount (language X) n) / n + Real.log (wordCount (language Y) n) / n := by
    have hpX : (wordCount (language X) n : ℝ) ≠ 0 := by
      exact_mod_cast (wordCount_pos_of_nonempty hX n).ne'
    have hpY : (wordCount (language Y) n : ℝ) ≠ 0 := by
      exact_mod_cast (wordCount_pos_of_nonempty hY n).ne'
    rw [wordCount_productShift, Nat.cast_mul, Real.log_mul hpX hpY, add_div]
  apply tendsto_nhds_unique (tendsto_entropy (productShift_nonempty hX hY))
  simpa only [hlog] using (tendsto_entropy hX).add (tendsto_entropy hY)
end BalanceSpecification
