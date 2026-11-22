-- Prove2me | solution 1 for DeciSigma1.Words.chain_stop_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:49.845836+00:00
-- url     : https://prove2.me/submissions/42e0f105-9297-4174-9a3a-2626eb11b0c5

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_suffixReturnGap_spec
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Words.length_suffixOfLength

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
theorem _root_.solution {t : List α} {b₀ S : ℕ} (hS : ChainBoundFrom t b₀ S) (g : ℕ → ℕ)
    (hg : Monotone g) {bs : ℕ} (hbs : b₀ ≤ bs) :
    ∃ b, bs ≤ b ∧ b ≤ (fun b => b + g b)^[S] bs ∧
      ∀ h, suffixReturnGap t b = some h → g b < h := by
  set G : ℕ → ℕ := fun b => b + g b with hG
  have hGm : Monotone G := fun a b hab => Nat.add_le_add hab (hg hab)
  have hGi : ∀ n b, b ≤ G^[n] b := by
    intro n
    induction n with
    | zero => intro b; simp
    | succ n ih =>
        intro b; rw [Function.iterate_succ_apply]; exact (Nat.le_add_right b _).trans (ih _)
  have claim : ∀ n b0, (∃ b, b0 ≤ b ∧ b ≤ G^[n] b0 ∧ ∀ h, suffixReturnGap t b = some h → g b < h) ∨
      ∃ l : List ℕ, SuffixChain t (b0 :: l) ∧ l.length = n + 1 := by
    intro n
    induction n with
    | zero =>
      intro b0
      by_cases hstop : ∀ h, suffixReturnGap t b0 = some h → g b0 < h
      · exact Or.inl ⟨b0, le_rfl, by simp, hstop⟩
      · push Not at hstop
        obtain ⟨h, hD, _⟩ := hstop
        have h1 := (suffixReturnGap_spec hD).2.1
        refine Or.inr ⟨[b0 + h], ?_, rfl⟩
        exact List.isChain_pair.mpr ⟨by rw [Nat.add_sub_cancel_left]; exact hD, by omega⟩
    | succ n ih =>
      intro b0
      by_cases hstop : ∀ h, suffixReturnGap t b0 = some h → g b0 < h
      · exact Or.inl ⟨b0, le_rfl, hGi _ _, hstop⟩
      · push Not at hstop
        obtain ⟨h, hD, hhg⟩ := hstop
        have h1 := (suffixReturnGap_spec hD).2.1
        rcases ih (b0 + h) with ⟨b, hb1, hb2, hb3⟩ | ⟨l, hl, hlen⟩
        · refine Or.inl ⟨b, by omega, hb2.trans ?_, hb3⟩
          rw [Function.iterate_succ_apply]
          exact Monotone.iterate hGm n (by simp only [G]; omega)
        · refine Or.inr ⟨(b0 + h) :: l, ?_, by simp [hlen]⟩
          exact List.isChain_cons_cons.mpr
            ⟨⟨by rw [Nat.add_sub_cancel_left]; exact hD, by omega⟩, hl⟩
  rcases claim S bs with hl | ⟨l, hl, hlen⟩
  · exact hl
  · have := hS bs l hbs hl
    omega
end DeciSigma1.Words
