-- Prove2me | solution 1 for BalanceSpecification.block_isInfix_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:43.472992+00:00
-- url     : https://prove2.me/submissions/0fd452c4-995b-458d-b476-3b3433c9886f

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_block_append
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution (x : Configuration A) (k l : ℤ) (n N : ℕ)
    (hleft : l ≤ k) (hright : k + n ≤ l + N) :
    block x k n <:+: block x l N := by
  let p := (k - l).toNat
  have hpc : (p : ℤ) = k - l := Int.toNat_of_nonneg (by omega)
  have hlen : p + n ≤ N := by omega
  let q := N - (p + n)
  have hN : p + n + q = N := by dsimp only [q]; omega
  have hk : l + (p : ℤ) = k := by omega
  have hkn : l + ((p + n : ℕ) : ℤ) = k + n := by
    simp only [Nat.cast_add]
    omega
  refine ⟨block x l p, block x (k + n) q, ?_⟩
  calc
    block x l p ++ block x k n ++ block x (k + n) q = block x l (p + n + q) := by
      rw [block_append, block_append, hk, hkn]
    _ = block x l N := by rw [hN]
end BalanceSpecification
