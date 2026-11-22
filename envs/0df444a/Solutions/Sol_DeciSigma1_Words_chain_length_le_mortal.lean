-- Prove2me | solution 1 for DeciSigma1.Words.chain_length_le_mortal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:41:00.980821+00:00
-- url     : https://prove2.me/submissions/d2db3740-6439-4adc-ab2d-9f3bdc717837

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_pairwise
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_le_length
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_length_le_card
public import Theorems.Thm_DeciSigma1_Words_two_le_card_of_eligible
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_runPrefix_ne_of_mortal


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
variable {S : Type} [Fintype S] {k : ℕ} (M : StructuralReader α S k)
  {W : Fin k → List α} {j : Fin k}
variable {M}
namespace DeciSigma1.Words
theorem _root_.solution (h : M.Eligible W j) (hm : ¬ M.Immortal (M.endState W j))
    {bs : List ℕ} (hbs : SuffixChain (W j) bs) : bs.length ≤ Fintype.card S - 1 := by
  classical
  by_cases h2 : 2 ≤ bs.length
  · have hle := hbs.le_length h2
    have hp := hbs.pairwise
    refine hbs.length_le_card (fun b => M.runPrefix W j ((W j).length - b)) M.dead ?_
      (fun b _ => h.runPrefix_ne _)
    intro b hb b' hb' hlt
    have hpre : (W j).drop ((W j).length - b) <+: (W j).drop ((W j).length - b') := by
      have := (List.pairwise_iff_getElem.mp hp)
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hb'
      have hii : i < i' := by
        rcases lt_trichotomy i i' with hlt' | rfl | hlt'
        · exact hlt'
        · omega
        · exact absurd (this i' i hi' hi hlt').1 (by omega)
      exact (this i i' hi hi' hii).2.2
    have := StructuralReader.runPrefix_ne_of_mortal h hm (a := (W j).length - b')
      (b := (W j).length - b)
      (by have := hle b hb; have := hle b' hb'; omega) (Nat.sub_le _ _) hpre
    exact fun he => this he.symm
  · have := two_le_card_of_eligible M h
    omega
end DeciSigma1.Words
