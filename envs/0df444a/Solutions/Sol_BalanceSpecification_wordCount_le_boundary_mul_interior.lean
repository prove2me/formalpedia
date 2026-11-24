-- Prove2me | solution 1 for BalanceSpecification.wordCount_le_boundary_mul_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:27.373729+00:00
-- url     : https://prove2.me/submissions/bb91fdfc-a88b-4abb-9d6e-11e703a43a14

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Theorems.Thm_BalanceSpecification_card_allWords
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution (L : Set (Word A)) (M t : ℕ) :
    wordCount L (2 * M + t) ≤ (Fintype.card A) ^ (2 * M) *
      wordCount (interiorLanguage L M) t := by
  classical
  have hcard : wordCount L (2 * M + t) ≤
      ((allWords (A := A) M).product
        ((wordFinset (interiorLanguage L M) t).product (allWords (A := A) M))).card := by
    apply Finset.card_le_card_of_injOn
      (fun w : Word A => (w.take M, (w.drop M).take t, (w.drop M).drop t))
    · intro w hw
      obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
      have hp : (w.take M).length = M := by
        simp only [List.length_take, hwlen]
        omega
      have hu : ((w.drop M).take t).length = t := by
        simp only [List.length_take, List.length_drop, hwlen]
        omega
      have hq : ((w.drop M).drop t).length = M := by
        simp only [List.length_drop, hwlen]
        omega
      have hglue : w.take M ++ (w.drop M).take t ++ (w.drop M).drop t = w := by
        rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
      apply Finset.mem_product.mpr
      refine ⟨mem_allWords.mpr hp, Finset.mem_product.mpr ⟨?_, mem_allWords.mpr hq⟩⟩
      apply mem_wordFinset.mpr
      exact ⟨⟨w.take M, (w.drop M).drop t, hp.ge, hq.ge, hglue.symm ▸ hwL⟩, hu⟩
    · intro v hv w hw h
      have hp := congrArg Prod.fst h
      have hu := congrArg (fun z : Word A × Word A × Word A => z.2.1) h
      have hq := congrArg (fun z : Word A × Word A × Word A => z.2.2) h
      have hrest : v.drop M = w.drop M := by
        calc
          v.drop M = (v.drop M).take t ++ (v.drop M).drop t :=
            (List.take_append_drop t (v.drop M)).symm
          _ = (w.drop M).take t ++ (w.drop M).drop t :=
            congrArg₂ (fun a b : Word A => a ++ b) hu hq
          _ = w.drop M := List.take_append_drop t (w.drop M)
      calc
        v = v.take M ++ v.drop M := (List.take_append_drop M v).symm
        _ = w.take M ++ w.drop M := congrArg₂ (fun a b : Word A => a ++ b) hp hrest
        _ = w := List.take_append_drop M w
  have hp : ((allWords (A := A) M).product
      ((wordFinset (interiorLanguage L M) t).product (allWords (A := A) M))).card =
      (allWords (A := A) M).card *
        ((wordFinset (interiorLanguage L M) t).card * (allWords (A := A) M).card) := by
    rw [Finset.product_eq_sprod, Finset.product_eq_sprod,
      Finset.card_product, Finset.card_product]
  rw [hp] at hcard
  calc
    wordCount L (2 * M + t) ≤ (Fintype.card A) ^ M *
        (wordCount (interiorLanguage L M) t * (Fintype.card A) ^ M) := by
      simpa only [card_allWords, wordCount] using hcard
    _ = (Fintype.card A) ^ (2 * M) * wordCount (interiorLanguage L M) t := by
      rw [two_mul, pow_add]
      ring
end BalanceSpecification
