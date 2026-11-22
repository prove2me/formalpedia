-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.isPeriodicPiece_deletePositions_with_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:59:27.019357+00:00
-- url     : https://prove2.me/submissions/39f6fc83-27f3-44a7-897a-7e336735513b

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_IsPrimitive_ne_nil
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono
public import Theorems.Thm_DeciSigma1_Words_retainedCount_succ_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {U U' : Fin k → List α} {l : Fin k}
    {Dl : Finset ℕ}
    (hU' : U' l = deletePositions (U l) Dl) {d s e : ℕ} (hc : IsPeriodicPiece U d l s e)
    (hin : ∀ p, s ≤ p → p < e → p ∉ Dl) (hleft : s ≠ 0 → s - 1 ∉ Dl)
    (hright : e < (U l).length → e ∉ Dl) :
    IsPeriodicPiece U' d l (retainedCount Dl s) (retainedCount Dl e) ∧ retainedCount Dl e =
        retainedCount Dl s + (e - s) ∧
      ((U' l).drop (retainedCount Dl s)).take d = ((U l).drop s).take d := by
  classical
  obtain ⟨hlong, hle, hper, hprim, hmaxL, hmaxR⟩ := hc
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact absurd (by simp [h]) hprim.ne_nil
    · exact h
  have hkeep : ∀ o ≤ e - s, retainedCount Dl (s + o) = retainedCount Dl s + o :=
    fun o ho => retainedCount_add_of_not_mem (fun i hi => hin _ (by omega) (by omega))
  have he : retainedCount Dl e = retainedCount Dl s + (e - s) := by
    have := hkeep (e - s) le_rfl
    rwa [show s + (e - s) = e by omega] at this
  have hget : ∀ o < e - s, (U' l)[retainedCount Dl s + o]? = (U l)[s + o]? := by
    intro o ho
    rw [← hkeep o ho.le, hU']
    exact getElem?_deletePositions _ (hin _ (by omega) (by omega)) (by omega)
  have hlen' : (U' l).length = retainedCount Dl (U l).length := by rw [hU', length_deletePositions]
  have hroot : ((U' l).drop (retainedCount Dl s)).take d = ((U l).drop s).take d := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < d
    · rw [List.getElem?_take_of_lt hi, List.getElem?_drop, hget i (by omega),
        List.getElem?_take_of_lt hi, List.getElem?_drop]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  refine ⟨⟨by omega, by rw [hlen']; exact retainedCount_mono hle, ?_, ?_, ?_, ?_⟩, he, hroot⟩
  · intro p _ hp hpe
    have h1 := hget (p - retainedCount Dl s) (by omega)
    have h2 := hget (p - retainedCount Dl s + d) (by omega)
    rw [show retainedCount Dl s + (p - retainedCount Dl s) = p by omega] at h1
    rw [show retainedCount Dl s + (p - retainedCount Dl s + d) = p + d by omega] at h2
    rw [h1, h2]
    simpa only [Nat.add_assoc] using hper (s + (p - retainedCount Dl s)) (by omega) (by omega)
        (by omega)
  · rw [hroot]; exact hprim
  · rcases hmaxL with hs | hs
    · left; rw [hs, retainedCount_zero]
    · by_cases hs0 : s = 0
      · left; rw [hs0, retainedCount_zero]
      · right
        have hk := retainedCount_succ_of_not_mem (hleft hs0)
        rw [show s - 1 + 1 = s by omega] at hk
        have hprev : (U' l)[retainedCount Dl s - 1]? = (U l)[s - 1]? := by
          rw [hk, Nat.add_sub_cancel, hU']
          exact getElem?_deletePositions _ (hleft hs0) (by omega)
        rw [hprev, show retainedCount Dl s - 1 + d = retainedCount Dl s + (d - 1) by omega,
            hget (d - 1) (by omega),
          show s + (d - 1) = s - 1 + d by omega]
        exact hs
  · rcases hmaxR with hE | hE
    · left; rw [hlen', hE]
    · by_cases hend : e = (U l).length
      · left; rw [hlen', hend]
      · right
        have hlast : (U' l)[retainedCount Dl e]? = (U l)[e]? := by
          rw [hU']; exact getElem?_deletePositions _ (hright (by omega)) (by omega)
        rw [hlast, he,
            show retainedCount Dl s + (e - s) - d = retainedCount Dl s + (e - s - d) by omega,
          hget (e - s - d) (by omega), show s + (e - s - d) = e - d by omega]
        exact hE
end DeciSigma1.Holes.Periodic
