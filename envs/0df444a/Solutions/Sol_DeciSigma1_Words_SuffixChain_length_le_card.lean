-- Prove2me | solution 1 for DeciSigma1.Words.SuffixChain.length_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:24.005518+00:00
-- url     : https://prove2.me/submissions/3e7b61e1-0970-4387-b83c-3acf1047e278

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_nodup

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
namespace SuffixChain
theorem _root_.solution {S : Type} [Fintype S] {t : List α}
    {bs : List ℕ} (h : SuffixChain t bs) (f : ℕ → S) (d : S)
    (hinj : ∀ b ∈ bs, ∀ b' ∈ bs, b < b' → f b ≠ f b') (hd : ∀ b ∈ bs, f b ≠ d) :
    bs.length ≤ Fintype.card S - 1 := by
  classical
  have hnd := h.nodup
  have hsub : bs.toFinset.image f ⊆ Finset.univ.erase d := by
    intro s hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_erase.mpr ⟨hd b (List.mem_toFinset.mp hb), Finset.mem_univ _⟩
  have hinj' : Set.InjOn f bs.toFinset := by
    intro b hb b' hb' he
    rw [Finset.mem_coe, List.mem_toFinset] at hb hb'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hinj b hb b' hb' hlt he
    · exact hinj b' hb' b hb hlt he.symm
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj', List.toFinset_card_of_nodup hnd,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
  exact this
end SuffixChain
end DeciSigma1.Words
