-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.follower_card_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:28.022362+00:00
-- url     : https://prove2.me/submissions/efaed231-efb1-440c-a5bf-3d39a7670959

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_mem_vertexWords
public import Theorems.Thm_BalanceSpecification_OneSidedExample_vertexWords_card
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_append
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_mem_language
public import Theorems.Thm_BalanceSpecification_OneSidedExample_mem_language_shift_iff_exists_walk
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
attribute [local simp] BalanceSpecification.mem_followerFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution {u : Word Alphabet} (hu : u ∈ language shift) (n : ℕ) :
    2 ^ n ≤ (followerFinset (language shift) u n).card := by
  obtain ⟨s, t, hwalk⟩ := mem_language_shift_iff_exists_walk.mp hu
  have hsub : vertexWords t n ⊆ followerFinset (language shift) u n := by
    intro w hw
    obtain ⟨hwlen, z, hwpath⟩ := mem_vertexWords.mp hw
    exact mem_followerFinset.mpr ⟨hwpath.mem_language, hwlen,
      (hwalk.append hwpath).mem_language⟩
  rw [← vertexWords_card t n]
  exact Finset.card_le_card hsub
end BalanceSpecification.OneSidedExample
