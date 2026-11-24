-- Prove2me | solution 1 for BalanceSpecification.sGap_hasVariableSpecification_of_bounded_gaps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:52.878959+00:00
-- url     : https://prove2.me/submissions/f0ca7edd-227b-489d-8b38-8cd0c8b37f64

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
    {S : Set ℕ} (hS : S.Nonempty) (hg : HasBoundedSuccessiveGaps S) :
    HasVariableSpecification (sGapShift S) := by
  obtain ⟨N, hN⟩ := (hasBoundedSuccessiveGaps_iff_uniform_right_completion hS).mp hg
  refine ⟨2 * N + 1, ?_⟩
  intro u hu v hv
  obtain ⟨a, b, ha, huRead⟩ := (mem_language_sGapShift_iff hS).mp hu
  obtain ⟨a', b', ha', huRead', hb'⟩ := huRead.exists_small_end hN ha
  obtain ⟨c, d, hc, hvRead⟩ := (mem_language_sGapShift_iff hS).mp hv
  obtain ⟨s, hs, hcs, hsc⟩ := hN c hc
  let bridge : Word Bool := List.replicate b' false ++ true :: List.replicate (s - c) false
  have hbridgeRead : GapRead S b' bridge c := by
    apply GapRead.append (by
      simpa only [Nat.zero_add] using GapRead.replicate_false (S := S) 0 b')
    apply GapRead.one hs
    simpa only [Nat.add_sub_of_le hcs] using GapRead.replicate_false (S := S) c (s - c)
  have hfull : u ++ bridge ++ v ∈ language (sGapShift S) :=
    (mem_language_sGapShift_iff hS).mpr
      ⟨a', d, ha', (huRead'.append hbridgeRead).append hvRead⟩
  refine ⟨bridge, ?_, ?_, hfull⟩
  · exact language_factorial (sGapShift S) (u := bridge) (v := u ++ bridge ++ v)
      ⟨u, v, rfl⟩ hfull
  · simp only [bridge, List.length_append, List.length_replicate, List.length_cons]
    omega
end BalanceSpecification
