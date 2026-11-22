-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.levelCoverProperty_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:29.452353+00:00
-- url     : https://prove2.me/submissions/69c1d7b2-6ec4-4dc8-a1f6-7317bea28bda

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_filter_covers_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_le_longestPeriodicSuffixLength
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_of_le_longestPeriodicSuffixLength
public import Theorems.Thm_DeciSigma1_Holes_Tail_coordinateCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_firstRejection_sub_lt_word
public import Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_of_window
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_le
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_period_extend_gcd
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {σ : ℕ} [DecidableEq α] [Fintype S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds σ k (Fintype.card S)) {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) {l : ℕ}
        (hK : LevelCoverProperty C l M W i) :
    LevelCoverProperty C (l + 1) M W i := by
  refine ⟨coordinateCover_mono C (Nat.le_succ l) hK.1, ?_⟩
  by_contra hge
  push Not at hge
  have hYK := C.terminalLengthBound_gt_cover l
  have hY1 : 0 < C.terminalLengthBound (l + 1) := by omega
  obtain ⟨s, p, hp, hpE, hs, hper, hYs⟩ := exists_of_le_longestPeriodicSuffixLength hY1 hge
  have hYm : C.terminalLengthBound l ≤ C.terminalLengthBound (l + 1) :=
      C.terminalLengthBound_mono (by omega)
  have hKt := hK.2
  by_cases hpl : p ≤ C.periodBound l
  · have := le_longestPeriodicSuffixLength hp hpl hs hper
    omega
  push Not at hpl
  obtain ⟨fs, hfl, hfv, hunc⟩ := hK.1
  have hJn : M.firstRejection W i ≤ (W i).length := StructuralReader.firstRejection_le h
  have hNp : Fintype.card S * p ≤ Fintype.card S * C.periodBound (l + 1) :=
      Nat.mul_le_mul_left _ hpE
  have hX : C.terminalLengthBound (l + 1) ≤ (W i).length - max s (M.firstRejection W i) +
      Fintype.card S * C.periodBound (l + 1) := by
    by_cases hsJ : M.firstRejection W i ≤ s
    · have : max s (M.firstRejection W i) = s := max_eq_left hsJ
      omega
    · have := firstRejection_sub_lt_word h hp hper (by omega) hJn
      have : max s (M.firstRejection W i) = M.firstRejection W i := max_eq_right (by omega)
      omega
  have hex : ∃ f ∈ fs, p + f.period ≤ f.stop - max (max s (M.firstRejection W i)) f.start := by
    by_contra hno
    push Not at hno
    set X := Finset.Ico (max s (M.firstRejection W i)) (W i).length with hXdef
    have hsplit := Finset.card_filter_add_card_filter_not (s := X) (p := Covers fs)
    have h1 : (X.filter (fun x => ¬ Covers fs x)).card ≤ C.uncoveredBound l := by
      refine le_trans (Finset.card_le_card ?_) hunc
      intro x hx
      simp only [X, uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
      exact ⟨⟨by omega, hx.1.2⟩, hx.2⟩
    have h2 : (X.filter (Covers fs)).card ≤ fs.length * (p + C.periodBound l) := by
      refine (card_filter_covers_le X fs).trans ?_
      have := List.sum_le_card_nsmul
        (fs.map (fun f => (X.filter (fun x => f.start ≤ x ∧ x < f.stop)).card))
            (p + C.periodBound l) (by
        intro y hy
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
        have hfv' := hfv f hf
        have hnf := hno f hf
        calc (X.filter (fun x => f.start ≤ x ∧ x < f.stop)).card
            ≤ (Finset.Ico (max (max s (M.firstRejection W i)) f.start) f.stop).card :=
              Finset.card_le_card (fun x hx => by
                simp only [X, Finset.mem_filter, Finset.mem_Ico] at hx ⊢; omega)
          _ = f.stop - max (max s (M.firstRejection W i)) f.start := Nat.card_Ico _ _
          _ ≤ p + C.periodBound l := by have := hfv'.2.1; omega)
      simpa using this
    have h3 : fs.length * (p + C.periodBound l) ≤ (C.pieceCountBase + 1) *
        (2 * C.periodBound (l + 1)) :=
      Nat.mul_le_mul hfl
          (by have : C.periodBound l ≤ C.periodBound (l + 1) := C.periodBound_mono (by omega);
              omega)
    have h4 : X.card = (W i).length - max s (M.firstRejection W i) := Nat.card_Ico _ _
    omega
  obtain ⟨f, hf, hfm⟩ := hex
  obtain ⟨hfp, hfE, hfe, hfper⟩ := hfv f hf
  have h1 : PeriodicOn (W i) p (max (max s (M.firstRejection W i)) f.start) f.stop :=
    hper.mono (by omega) hfe
  have h2 : PeriodicOn (W i) f.period (max (max s (M.firstRejection W i)) f.start) f.stop :=
    hfper.mono (le_max_right _ _) le_rfl
  have hgle : p.gcd f.period ≤ f.period := Nat.gcd_le_right _ hfp
  have hgpos : 0 < p.gcd f.period := Nat.gcd_pos_of_pos_left _ hp
  have hg := period_extend_gcd (by omega) hfe h1 h2 (by omega)
  have hwin := periodicOn_of_window hper hg (by omega) hfe (by omega) hp
  have := le_longestPeriodicSuffixLength hgpos (hgle.trans hfE) hs hwin
  omega
end DeciSigma1.Holes.Tail
