-- Prove2me | solution 1 for BalanceSpecification.sGap_hasSpecification_of_bounded_gaps_of_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:15.32224+00:00
-- url     : https://prove2.me/submissions/5d1173dc-aadf-47d0-b3d5-f1b318b36ea9

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_GapRead_append
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_false
public import Theorems.Thm_BalanceSpecification_mem_language_sGapShift_iff
public import Theorems.Thm_BalanceSpecification_GapRead_exists_small_end
public import Theorems.Thm_BalanceSpecification_GapRead_replicate_true
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_hasBoundedSuccessiveGaps_iff_uniform_right_completion
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (h0 : 0 ∈ S) (hg : HasBoundedSuccessiveGaps S) :
    HasSpecification (sGapShift S) := by
  have hS : S.Nonempty := ⟨0, h0⟩
  obtain ⟨N, hN⟩ := (hasBoundedSuccessiveGaps_iff_uniform_right_completion hS).mp hg
  refine ⟨2 * N + 1, ?_⟩
  intro u hu v hv
  obtain ⟨a, b, ha, huRead⟩ := (mem_language_sGapShift_iff hS).mp hu
  obtain ⟨a', b', ha', huRead', hb'⟩ := huRead.exists_small_end hN ha
  obtain ⟨c, d, hc, hvRead⟩ := (mem_language_sGapShift_iff hS).mp hv
  obtain ⟨s, hs, hcs, hsc⟩ := hN c hc
  let pad := 2 * N + 1 - (b' + 1 + (s - c))
  let bridge : Word Bool :=
    List.replicate b' false ++ List.replicate pad true ++ true :: List.replicate (s - c) false
  have hzeros : GapRead S b' (List.replicate b' false) 0 := by
    simpa only [Nat.zero_add] using GapRead.replicate_false (S := S) 0 b'
  have hlast : GapRead S 0 (true :: List.replicate (s - c) false) c := by
    apply GapRead.one hs
    simpa only [Nat.add_sub_of_le hcs] using GapRead.replicate_false (S := S) c (s - c)
  have hbridgeRead : GapRead S b' bridge c :=
    (hzeros.append (GapRead.replicate_true h0 pad)).append hlast
  have hfull : u ++ bridge ++ v ∈ language (sGapShift S) :=
    (mem_language_sGapShift_iff hS).mpr
      ⟨a', d, ha', (huRead'.append hbridgeRead).append hvRead⟩
  refine ⟨bridge, ?_, ?_, hfull⟩
  · exact language_factorial (sGapShift S) (u := bridge) (v := u ++ bridge ++ v)
      ⟨u, v, rfl⟩ hfull
  · simp only [bridge, pad, List.length_append, List.length_replicate, List.length_cons]
    omega
end BalanceSpecification
