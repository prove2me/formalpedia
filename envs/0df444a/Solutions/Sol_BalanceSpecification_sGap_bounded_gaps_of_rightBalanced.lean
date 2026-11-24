-- Prove2me | solution 1 for BalanceSpecification.sGap_bounded_gaps_of_rightBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:11.481933+00:00
-- url     : https://prove2.me/submissions/98113758-2f93-400d-b2b0-20e3b42248b7

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty
public import Theorems.Thm_BalanceSpecification_finite_gapSet_of_finite_sGapShift
public import Theorems.Thm_BalanceSpecification_sGap_follower_eq_replicate_of_successive_gap
public import Theorems.Thm_BalanceSpecification_sGap_prefix_in_language
public import Theorems.Thm_BalanceSpecification_exists_large_successive_gap
public import Theorems.Thm_BalanceSpecification_finite_carrier_of_bounded_wordCount
public import Theorems.Thm_BalanceSpecification_infinite_of_not_hasBoundedSuccessiveGaps
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty
public import Theorems.Thm_BalanceSpecification_wordCount_zero_le_one
attribute [local simp] BalanceSpecification.mem_followerFinset



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) (hR : RightBalanced (language (sGapShift S))) :
    HasBoundedSuccessiveGaps S := by
  classical
  by_contra hnot
  obtain ⟨c, hc, hbound⟩ := hR
  have hcounts (n : ℕ) (hn : 1 ≤ n) :
      (wordCount (language (sGapShift S)) n : ℝ) ≤ 1 / c := by
    obtain ⟨a, ha, b, hb, hab, hnext, hgap⟩ := exists_large_successive_gap hnot n
    let u : Word Bool := true :: List.replicate (a + 1) false
    have hu : u ∈ language (sGapShift S) := sGap_prefix_in_language hS hb (by omega)
    have hcard : (followerFinset (language (sGapShift S)) u n).card ≤ 1 := by
      calc
        (followerFinset (language (sGapShift S)) u n).card ≤
            ({List.replicate n false} : Finset (Word Bool)).card := by
          apply Finset.card_le_card
          intro w hw
          obtain ⟨_, hwlen, huw⟩ := mem_followerFinset.mp hw
          exact Finset.mem_singleton.mpr
            (sGap_follower_eq_replicate_of_successive_gap hS hnext hgap huw hwlen)
        _ = 1 := Finset.card_singleton _
    have hpos : (0 : ℝ) < wordCount (language (sGapShift S)) n := by
      exact_mod_cast wordCount_pos_of_nonempty (sGapShift_nonempty hS) n
    have hlow := (le_div_iff₀ hpos).mp (hbound u hu n hn)
    have hcardR : ((followerFinset (language (sGapShift S)) u n).card : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    apply (le_div_iff₀ hc).mpr
    linarith only [hlow, hcardR]
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / c)
  have hfinite : (sGapShift S).carrier.Finite := by
    apply finite_carrier_of_bounded_wordCount
    refine ⟨max N 1, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      exact (wordCount_zero_le_one _).trans (le_max_right _ _)
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hNcount : wordCount (language (sGapShift S)) n ≤ N := by
        exact_mod_cast (hcounts n hn1).trans hN
      exact hNcount.trans (le_max_left _ _)
  exact (infinite_of_not_hasBoundedSuccessiveGaps hnot) (finite_gapSet_of_finite_sGapShift hfinite)
end BalanceSpecification
