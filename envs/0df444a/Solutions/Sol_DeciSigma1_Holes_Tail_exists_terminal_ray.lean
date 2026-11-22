-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_terminal_ray
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:01:58.007805+00:00
-- url     : https://prove2.me/submissions/622f5bed-37c0-48a7-adbb-b6e565dec713

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Theorems.Thm_DeciSigma1_Holes_Tail_runPrefix_period_stable
public import Theorems.Thm_DeciSigma1_Holes_Tail_iterate_add_const
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_of_le_longestPeriodicSuffixLength
public import Theorems.Thm_DeciSigma1_Holes_Tail_firstRejection_sub_lt_word
public import Theorems.Thm_DeciSigma1_Holes_Tail_noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_le
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_le_add
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_chain_stop
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_suffixReturnGap_mono
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
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {σ : ℕ} [DecidableEq α] [Fintype S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds σ k (Fintype.card S)) {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) {m : ℕ}
    (hT : C.terminalLengthBound m ≤ longestPeriodicSuffixLength (C.periodBound m) (W i)) :
    ∃ B c p, ClosedAt M.toTable (M.start i) (W i) B c (W i).length ∧ M.firstRejection W i ≤ c ∧
      0 < p ∧ p ≤ C.periodBound m ∧ (W i).length - c = p * (Fintype.card S).factorial ∧
      PeriodicOn (W i) p (c - B) (W i).length ∧
      ∀ t : List α, ChainBound t (C.fixedChainBudget (m + 1)) →
          NoSuffixOccurrenceEndsBetween (W i) t B c (W i).length := by
  have hbud := C.terminalLengthBound_ge_periodBudget m
  have hY : 0 < C.terminalLengthBound m := by omega
  obtain ⟨s, p, hp, hpE, hs, hper, hYs⟩ := exists_of_le_longestPeriodicSuffixLength hY hT
  have hfac : 0 < (Fintype.card S).factorial := Nat.factorial_pos _
  have hh0 : 0 < p * (Fintype.card S).factorial := Nat.mul_pos hp hfac
  have hh0le : p * (Fintype.card S).factorial ≤ C.periodBound m * (Fintype.card S).factorial :=
    Nat.mul_le_mul_right _ hpE
  have hSl : C.fixedChainBudget (m + 1) * (p * (Fintype.card S).factorial) ≤
      C.fixedChainBudget (m + 1) * (C.periodBound m * (Fintype.card S).factorial) :=
          Nat.mul_le_mul_left _ hh0le
  have hNp : Fintype.card S * p ≤ Fintype.card S * C.periodBound m := Nat.mul_le_mul_left _ hpE
  have hcomm : (Fintype.card S).factorial * p = p * (Fintype.card S).factorial := Nat.mul_comm _ _
  set h0 := p * (Fintype.card S).factorial with hh0def
  set B0 := 1 + C.fixedChainBudget (m + 1) * h0 with hB0
  set n := (W i).length with hn
  have hlong : s + (B0 + h0) + h0 + Fintype.card S * p ≤ n := by omega
  have hcl : ClosedAt M.toTable (M.start i) (W i) (B0 + h0) (n - h0) n := by
    refine ⟨by omega, by omega, le_rfl, ?_⟩
    have hst : M.runPrefix W i (n - h0 - (B0 + h0) + h0) = M.runPrefix W i (n - h0 - (B0 + h0)) :=
      runPrefix_period_stable M.toTable W i hp hper le_rfl (by omega) (by omega)
    rw [show n - h0 - (B0 + h0) + h0 = n - (B0 + h0) by omega] at hst
    simp only [windowState]
    refine Prod.ext hst.symm ?_
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_drop, List.getElem?_take]
    by_cases hj : j < B0 + h0
    · rw [if_pos (by omega), if_pos (by omega)]
      have := hper.eq_of_le_add (p := n - h0 - (B0 + h0) + j) (by omega)
        (Fintype.card S).factorial (by omega)
      rw [this]; congr 1; omega
    · rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨B0 + h0, n - h0, p, hcl, ?_, hp, hpE, by omega, hper.mono (by omega) le_rfl, ?_⟩
  · by_cases hsJ : M.firstRejection W i ≤ s
    · omega
    · have := firstRejection_sub_lt_word h hp hper (by omega) (StructuralReader.firstRejection_le h)
      omega
  · intro t ht
    obtain ⟨b, hb1, hb2, hstop⟩ := chain_stop ht (fun _ => h0) (fun _ _ _ => le_rfl) 1
    have hb2' : b ≤ B0 := by
      have := iterate_add_const h0 1 (C.fixedChainBudget (m + 1))
      rw [this] at hb2
      omega
    apply noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt hcl (B := B0) (by omega)
    intro h' hD'
    obtain ⟨h'', hD'', hle⟩ := suffixReturnGap_mono hb2' hD'
    have := hstop h'' hD''
    omega
end DeciSigma1.Holes.Tail
