-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_closed_factor_free_of_suffix_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:53:16.764488+00:00
-- url     : https://prove2.me/submissions/d0cd342c-7e08-40b2-8e25-f16cb9a73e93

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_cons
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_cons
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixReturnGap_le_of_two_occ
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_suffixDictionary_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_nodeClosedAt_of_spaced_cuts
public import Theorems.Thm_DeciSigma1_Holes_Tail_nil_mem_suffixDictionary
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_chain_stop_from
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_occurrences_antitone
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S]
variable (T : Readers.Table α S k) (q0 : S) (x : List α)
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (ds : List (List α)) {m : ℕ}
    (hm : ds.length ≤ m) (b₀ : ℕ) :
    ∀ (ts : List (List α)) (Ss : List ℕ), List.Forall₂ (fun t S => ChainBoundFrom t b₀ S) ts Ss →
    ∀ bs u, b₀ ≤ bs → u + suffixLengthBound m (Fintype.card S) Ss bs ≤ x.length + 1 →
      ∃ B c c', bs ≤ B ∧ B ≤ suffixLengthEnvelope m (Fintype.card S) Ss bs ∧ u ≤ c ∧
        c' < u + suffixLengthBound m (Fintype.card S) Ss bs ∧
            NodeClosedAt T q0 (suffixDictionary ds B) x c c' ∧
        (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween x t B c c') ∧ B < c' - c ∧
          c' - c ≤ factorLengthBound m (Fintype.card S) B := by
  intro ts Ss hS
  induction hS with
  | nil =>
    intro bs u _ hu
    simp only [suffixLengthBound_nil] at hu ⊢
    have hcard : (suffixDictionary ds bs).card * Fintype.card S ≤
        suffixNodeBound m (Fintype.card S) bs := by
      rw [suffixNodeBound, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ ((card_suffixDictionary_le ds bs).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ hm) 1))
    have hV : (bs + 1) * ((suffixDictionary ds bs).card * Fintype.card S) ≤
        factorLengthBound m (Fintype.card S) bs := Nat.mul_le_mul_left _ hcard
    obtain ⟨c, c', hc, hc', hsp, hcl⟩ := exists_nodeClosedAt_of_spaced_cuts T q0
      (D := suffixDictionary ds bs) nil_mem_suffixDictionary x (s := bs + 1) (u := u) (by omega)
      (by omega)
    exact ⟨bs, c, c', le_rfl, le_rfl, hc, by omega, hcl, by simp, by omega, by omega⟩
  | @cons t Sb ts Ss hSt hrest ih =>
    intro bs u hb₀ hu
    set N := Fintype.card S
    set g := suffixLengthBound m N Ss with hg
    have hgm : Monotone g := suffixLengthBound_mono m N Ss
    set bstar := (fun b => b + g b)^[Sb] bs with hbstar
    have hL : suffixLengthBound m N (Sb :: Ss) bs = 2 * g bstar + g (bstar + g bstar) + 2 :=
        suffixLengthBound_cons m N Sb Ss bs
    have hF : suffixLengthEnvelope m N (Sb :: Ss) bs =
        suffixLengthEnvelope m N Ss (bstar + g bstar) := suffixLengthEnvelope_cons m N Sb Ss bs
    rw [hL] at hu ⊢
    rw [hF]
    obtain ⟨b, hbs, hbb, hstop⟩ := chain_stop_from hSt g hgm hb₀
    have hgb : g b ≤ g bstar := hgm hbb
    have hgb' : g (b + g b) ≤ g (bstar + g bstar) := hgm (Nat.add_le_add hbb hgb)
    have hFb : ∀ b', b' ≤ bstar + g bstar → suffixLengthEnvelope m N Ss b' ≤
        suffixLengthEnvelope m N Ss (bstar + g bstar) :=
      fun b' h => suffixLengthEnvelope_mono m N Ss h
    by_cases hcase : ∃ u', u ≤ u' ∧ u' + g b ≤ u + (2 * g bstar + g (bstar + g bstar) + 2) ∧
        ∀ e ∈ occurrences x t b, e < u' ∨ u' + g b ≤ e
    · -- case 1: `g b` consecutive cuts outside `occurrences x t b`
      obtain ⟨u', hu1, hu2, hfree⟩ := hcase
      obtain ⟨B, c, c', hB1, hB2, hc, hc', hcl, hts, hgap⟩ := ih b u' (by omega) (by omega)
      refine ⟨B, c, c', hbs.trans hB1, hB2.trans (hFb b (by omega)), by omega, by omega, hcl,
        ?_, hgap⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · refine NoSuffixOccurrenceEndsBetween.mono (fun e he => ?_) hB1
        rcases hfree e he with h | h <;> omega
      · exact hts t' ht'
    · -- case 2: the first occurrence is early and later ones are dense
      push Not at hcase
      obtain ⟨e0, he0, h01, h02⟩ := hcase u le_rfl (by omega)
      have hne : ((occurrences x t b).filter (fun e => u ≤ e)).Nonempty :=
        ⟨e0, Finset.mem_filter.mpr ⟨he0, h01⟩⟩
      set e1 := ((occurrences x t b).filter (fun e => u ≤ e)).min' hne with he1
      have he1mem := Finset.min'_mem _ hne
      rw [← he1, Finset.mem_filter] at he1mem
      have he1min : ∀ e ∈ occurrences x t b, u ≤ e → e1 ≤ e := fun e he hue =>
        Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨he, hue⟩)
      have he1u : e1 < u + g b := (he1min e0 he0 h01).trans_lt h02
      -- no end of `v_{b + g b}` after `e1`
      have hnone : ∀ e, e1 < e → e < u + (2 * g bstar + g (bstar + g bstar) + 2) →
          e ∉ occurrences x t (b + g b) := by
        intro e he1e heu he
        have heb : e ∈ occurrences x t b := occurrences_antitone (Nat.le_add_right _ _) he
        have hne' : ((occurrences x t b).filter (fun y => y < e)).Nonempty :=
          ⟨e1, Finset.mem_filter.mpr ⟨he1mem.1, he1e⟩⟩
        set e' := ((occurrences x t b).filter (fun y => y < e)).max' hne' with he'
        have he'mem := Finset.max'_mem _ hne'
        rw [← he', Finset.mem_filter] at he'mem
        have he'max : ∀ y ∈ occurrences x t b, y < e → y ≤ e' := fun y hy hye =>
          Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hy, hye⟩)
        have he1e' : e1 ≤ e' := he'max e1 he1mem.1 he1e
        have hgap : e - e' ≤ g b := by
          by_contra hgt
          obtain ⟨y, hy, h1, h2⟩ := hcase (e' + 1) (by omega) (by omega)
          have := he'max y hy (by omega)
          omega
        obtain ⟨h0, hD, hle⟩ := suffixReturnGap_le_of_two_occ he he'mem.1 he'mem.2 hgap
        have := hstop h0 hD
        omega
      obtain ⟨B, c, c', hB1, hB2, hc, hc', hcl, hts, hgapB⟩ :=
        ih (b + g b) (e1 + 1) (by omega) (by omega)
      refine ⟨B, c, c', by omega, hB2.trans (hFb _ (by omega)), by omega, by omega, hcl, ?_,
        hgapB⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · refine NoSuffixOccurrenceEndsBetween.mono (fun e he => ?_) hB1
        by_contra hcon
        push Not at hcon
        exact hnone e (by omega) (by omega) he
      · exact hts t' ht'
end DeciSigma1.Holes.Tail
