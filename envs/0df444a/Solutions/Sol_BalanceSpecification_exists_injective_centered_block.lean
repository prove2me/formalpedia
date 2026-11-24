-- Prove2me | solution 1 for BalanceSpecification.exists_injective_centered_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:53:49.7938+00:00
-- url     : https://prove2.me/submissions/8707365e-af76-4969-b0c2-05309329820a

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
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
namespace BalanceSpecification
theorem _root_.solution (s : Finset (Configuration A)) :
    ∃ M : ℕ, Set.InjOn (fun x => block x (-(M : ℤ)) (2 * M + 1)) (s : Set (Configuration A)) := by
  classical
  have hdiff : ∀ z : Configuration A × Configuration A,
      z.1 ≠ z.2 → ∃ i : ℤ, z.1 i ≠ z.2 i := by
    intro z hne
    by_contra h
    push Not at h
    exact hne (funext h)
  let d : Configuration A × Configuration A → ℤ :=
    fun z => if h : z.1 = z.2 then 0 else Classical.choose (hdiff z h)
  have hd : ∀ z : Configuration A × Configuration A, z.1 ≠ z.2 → z.1 (d z) ≠ z.2 (d z) := by
    intro z hz
    simp only [d, dif_neg hz]
    exact Classical.choose_spec (hdiff z hz)
  let M : ℕ := ∑ z ∈ s.product s, (d z).natAbs
  refine ⟨M, ?_⟩
  intro x hx y hy hblocks
  by_contra hne
  have habs : (d (x, y)).natAbs ≤ M := by
    change (d (x, y)).natAbs ≤ ∑ z ∈ s.product s, (d z).natAbs
    exact Finset.single_le_sum (f := fun z => (d z).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_product.mpr ⟨hx, hy⟩)
  have hu : d (x, y) ≤ ((d (x, y)).natAbs : ℤ) := Int.le_natAbs
  have hl : -(d (x, y)) ≤ ((d (x, y)).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -d (x, y)))
  let j : ℕ := ((M : ℤ) + d (x, y)).toNat
  have hjcast : (j : ℤ) = (M : ℤ) + d (x, y) := by
    apply Int.toNat_of_nonneg
    omega
  have hj : j < 2 * M + 1 := by omega
  have he := List.getElem_of_eq hblocks
    (show j < (block x (-(M : ℤ)) (2 * M + 1)).length by simpa only [length_block] using hj)
  simp only [block, List.getElem_ofFn] at he
  have hecast : -(M : ℤ) + (j : ℤ) = d (x, y) := by omega
  exact hd (x, y) hne (by simpa only [hecast] using he)
end BalanceSpecification
