-- Prove2me | solution 1 for BalanceSpecification.wordCount_le_ncard_of_finite_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:12.574495+00:00
-- url     : https://prove2.me/submissions/0c329619-f069-42e5-b291-882e52aaf854

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_block_mem_language
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
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Finite) (n : ℕ) :
    wordCount (language X) n ≤ X.carrier.ncard := by
  classical
  have himage : wordFinset (language X) n =
      hX.toFinset.image (fun x => block x 0 n) := by
    ext w
    constructor
    · intro hw
      obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
      obtain ⟨x, hx, hxblock⟩ := mem_language_iff_exists_block_zero.mp hwL
      exact Finset.mem_image.mpr ⟨x, hX.mem_toFinset.mpr hx, by simpa only [hwlen] using hxblock⟩
    · intro hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
      exact mem_wordFinset.mpr ⟨block_mem_language (hX.mem_toFinset.mp hx) 0 n,
        length_block _ _ _⟩
  unfold wordCount
  rw [himage]
  exact (Finset.card_image_le).trans_eq (Set.ncard_eq_toFinset_card X.carrier hX).symm
end BalanceSpecification
