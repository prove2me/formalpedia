-- Prove2me | solution 1 for DeciSigma1.Words.suffixReturnGap_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:09.011451+00:00
-- url     : https://prove2.me/submissions/35859cb4-db32-465c-8822-ba371c806eec

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_suffixOfLength_suffix_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_suffixReturnGap_spec
public import Theorems.Thm_DeciSigma1_Words_suffixReturnGap_le_of_occ
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
theorem _root_.solution {t : List α} {b b' h' : ℕ} (hbb : b ≤ b')
    (hD : suffixReturnGap t b' = some h') :
    ∃ h, suffixReturnGap t b = some h ∧ h ≤ h' := by
  obtain ⟨hb', h1, h2, hocc⟩ := suffixReturnGap_spec hD
  exact suffixReturnGap_le_of_occ (hbb.trans hb') h1 (by omega)
      ((suffixOfLength_suffix_suffixOfLength t hbb).trans hocc)
end DeciSigma1.Words
