-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.full_suppressed_epoch_coupling
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:55:20.530373+00:00
-- url     : https://prove2.me/submissions/a1e1b8cc-05b5-47c5-a9c6-c20d0c89bf55

import Definitions.Def_CountingLLL_ReciprocalWalkEpoch
import Theorems.Thm_CountingLLL_ReciprocalTest_full_suppressed_first_change
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private def WalkPhase : Phase → Prop
  | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
  | .uniformCheck | .done _ => True
  | _ => False

/-- At nonsticking tapes, erased-change epochs follow the abstract contracted walk pathwise. -/
private theorem suppressed_epoch_level_coupling (ω : Entropy) (start : ℕ)
    (hphase : WalkPhase (allSuppressedRun ω start).phase)
    (hprogress : ∀ n, (allSuppressedRun ω (changeEpoch ω start n)).i ≠ 0 →
      ∃ k, changeEpoch ω start n < k ∧
        (allSuppressedRun ω k).i ≠ (allSuppressedRun ω (changeEpoch ω start n)).i) :
    ∀ n, (allSuppressedRun ω (changeEpoch ω start n)).i =
      CountingLLL.ContractedWalk.level (changeDirection ω start) (allSuppressedRun ω start).i n ∧
      WalkPhase (allSuppressedRun ω (changeEpoch ω start n)).phase := by
  classical
  intro n
  induction n with
  | zero => simpa [changeEpoch, CountingLLL.ContractedWalk.level] using hphase
  | succ n ih =>
    let t := changeEpoch ω start n
    by_cases hz : (allSuppressedRun ω t).i = 0
    · have he : changeEpoch ω start (n+1) = t := by simp [changeEpoch, nextChangeTime,t,hz]
      have hl : CountingLLL.ContractedWalk.level (changeDirection ω start) (allSuppressedRun ω start).i n = 0 := by
        rw [← ih.1]; exact hz
      rw [he]
      constructor
      · simp [CountingLLL.ContractedWalk.level,hl,hz]
      · exact ih.2
    · have hex : ∃ k, t < k ∧ (allSuppressedRun ω k).i ≠ (allSuppressedRun ω t).i := hprogress n hz
      have he : changeEpoch ω start (n+1) = Nat.find hex := by simp [changeEpoch,nextChangeTime,t,hz,hex]
      have hspec := Nat.find_spec hex
      have hconst : ∀ k, t < k → k < Nat.find hex → (allSuppressedRun ω k).i = (allSuppressedRun ω t).i := by
        intro k htk hkn
        by_contra hne
        exact (Nat.find_min hex hkn) ⟨htk,hne⟩
      have hc := full_suppressed_first_change ω t (Nat.find hex) hspec.1 ih.2 hconst hspec.2
      rw [he]
      have hdirection : changeDirection ω start n =
          (if (allSuppressedRun ω (Nat.find hex)).i = (allSuppressedRun ω t).i + 2 then true else false) := by
        simp [changeDirection, he, t]
      rw [CountingLLL.ContractedWalk.level, ← ih.1]
      change (allSuppressedRun ω (Nat.find hex)).i =
          (if (allSuppressedRun ω t).i = 0 then 0 else
            if changeDirection ω start n then (allSuppressedRun ω t).i + 2 else (allSuppressedRun ω t).i - 1) ∧ _
      rw [if_neg hz, hdirection]
      rcases hc.1 with hd | hu
      · have hne : (allSuppressedRun ω (Nat.find hex)).i ≠ (allSuppressedRun ω t).i + 2 := by omega
        constructor
        · simp [hne, hd.1]
        · exact hc.2
      · constructor
        · simp [hu.1]
        · exact hc.2

/-- The second counter is the initial value plus the number of upward changes. -/
private theorem suppressed_epoch_count_coupling (ω : Entropy) (start : ℕ)
    (hphase : WalkPhase (allSuppressedRun ω start).phase)
    (hprogress : ∀ n, (allSuppressedRun ω (changeEpoch ω start n)).i ≠ 0 →
      ∃ k, changeEpoch ω start n < k ∧
        (allSuppressedRun ω k).i ≠ (allSuppressedRun ω (changeEpoch ω start n)).i) :
    ∀ n, (allSuppressedRun ω (changeEpoch ω start n)).j =
      (allSuppressedRun ω start).j + ∑ t ∈ Finset.range n, (if changeDirection ω start t then 1 else 0 : ℕ) := by
  classical
  intro n
  induction n with
  | zero => simp [changeEpoch]
  | succ n ih =>
    let t := changeEpoch ω start n
    have hp := (suppressed_epoch_level_coupling ω start hphase hprogress n).2
    by_cases hz : (allSuppressedRun ω t).i = 0
    · have he : changeEpoch ω start (n+1) = t := by simp [changeEpoch, nextChangeTime,t,hz]
      have hd : changeDirection ω start n = false := by simp [changeDirection, he,t,hz]
      rw [he,Finset.sum_range_succ,hd]
      simpa [t] using ih
    · have hex : ∃ k, t < k ∧ (allSuppressedRun ω k).i ≠ (allSuppressedRun ω t).i := hprogress n hz
      have he : changeEpoch ω start (n+1) = Nat.find hex := by simp [changeEpoch,nextChangeTime,t,hz,hex]
      have hspec := Nat.find_spec hex
      have hconst : ∀ k, t < k → k < Nat.find hex → (allSuppressedRun ω k).i = (allSuppressedRun ω t).i := by
        intro k htk hkn
        by_contra hne
        exact (Nat.find_min hex hkn) ⟨htk,hne⟩
      have hc := full_suppressed_first_change ω t (Nat.find hex) hspec.1 hp hconst hspec.2
      have hdirection : changeDirection ω start n =
          (if (allSuppressedRun ω (Nat.find hex)).i = (allSuppressedRun ω t).i + 2 then true else false) := by
        simp [changeDirection, he, t]
      rw [he,Finset.sum_range_succ,hdirection]
      rcases hc.1 with hd | hu
      · have hne : (allSuppressedRun ω (Nat.find hex)).i ≠ (allSuppressedRun ω t).i + 2 := by omega
        simp only [if_neg hne, Bool.false_eq_true, ↓reduceIte, add_zero]
        rw [hd.2]
        exact ih
      · simp only [hu.1, ↓reduceIte]
        rw [hu.2, ih]
        omega


theorem solution (ω : Entropy) (start : ℕ)
    (hphase : (match (allSuppressedRun ω start).phase with
      | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
      | .uniformCheck | .done _ => True | _ => False))
    (hprogress : ∀ n, (allSuppressedRun ω (changeEpoch ω start n)).i ≠ 0 →
      ∃ k, changeEpoch ω start n < k ∧
        (allSuppressedRun ω k).i ≠ (allSuppressedRun ω (changeEpoch ω start n)).i) :
    ∀ n, (allSuppressedRun ω (changeEpoch ω start n)).i =
      CountingLLL.ContractedWalk.level (changeDirection ω start) (allSuppressedRun ω start).i n ∧
      (allSuppressedRun ω (changeEpoch ω start n)).j =
        (allSuppressedRun ω start).j + ∑ t ∈ Finset.range n, (if changeDirection ω start t then 1 else 0 : ℕ) := by
  change WalkPhase (allSuppressedRun ω start).phase at hphase
  intro n
  exact ⟨(suppressed_epoch_level_coupling ω start hphase hprogress n).1,
    suppressed_epoch_count_coupling ω start hphase hprogress n⟩
