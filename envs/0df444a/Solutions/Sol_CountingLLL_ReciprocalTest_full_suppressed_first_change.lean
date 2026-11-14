-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.full_suppressed_first_change
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:27.66898+00:00
-- url     : https://prove2.me/submissions/9444be25-6733-41d4-8c68-cd39588c25fe

import Theorems.Thm_CountingLLL_ReciprocalTest_full_suppressed_walk_step
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private def WalkPhase : Phase → Prop
  | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
  | .uniformCheck | .done _ => True
  | _ => False

private theorem step_walk (ω : Entropy) (s : State) (hs : WalkPhase s.phase) :
    WalkPhase (allSuppressedStep ω s).phase ∧
    (((allSuppressedStep ω s).i = s.i ∧ (allSuppressedStep ω s).j = s.j) ∨
     ((allSuppressedStep ω s).i = s.i - 1 ∧ (allSuppressedStep ω s).j = s.j) ∨
     ((allSuppressedStep ω s).i = s.i + 2 ∧ (allSuppressedStep ω s).j = s.j + 1)) := by
  exact full_suppressed_walk_step ω s hs

private theorem next (ω : Entropy) (n : ℕ) :
    allSuppressedRun ω (n+1) = allSuppressedStep ω (allSuppressedRun ω n) := by
  simp [allSuppressedRun, Function.iterate_succ_apply']

/-- Removing the silent steps preserves exactly the source walk's counter changes. -/
theorem solution (ω : Entropy) (m n : ℕ) (hmn : m < n)
    (hphase : (match (allSuppressedRun ω m).phase with
    | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
    | .uniformCheck | .done _ => True | _ => False))
    (hconstant : ∀ t, m < t → t < n → (allSuppressedRun ω t).i = (allSuppressedRun ω m).i)
    (hchange : (allSuppressedRun ω n).i ≠ (allSuppressedRun ω m).i) :
    (((allSuppressedRun ω n).i = (allSuppressedRun ω m).i - 1 ∧
       (allSuppressedRun ω n).j = (allSuppressedRun ω m).j) ∨
     ((allSuppressedRun ω n).i = (allSuppressedRun ω m).i + 2 ∧
       (allSuppressedRun ω n).j = (allSuppressedRun ω m).j + 1)) ∧
    (match (allSuppressedRun ω n).phase with
    | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
    | .uniformCheck | .done _ => True | _ => False) := by
  change WalkPhase (allSuppressedRun ω m).phase at hphase
  change _ ∧ WalkPhase (allSuppressedRun ω n).phase
  have hprefix (r : ℕ) (hr : m+r < n) :
      (allSuppressedRun ω (m+r)).i = (allSuppressedRun ω m).i ∧
      (allSuppressedRun ω (m+r)).j = (allSuppressedRun ω m).j ∧
      WalkPhase (allSuppressedRun ω (m+r)).phase := by
    induction r with
    | zero => simpa using hphase
    | succ r ih =>
      have hi := ih (by omega)
      have ht := step_walk ω (allSuppressedRun ω (m+r)) hi.2.2
      have hnext : (allSuppressedRun ω (m+r+1)).i = (allSuppressedRun ω m).i :=
        hconstant (m+r+1) (by omega) (by omega)
      rw [← next ω (m+r)] at ht
      have hj : (allSuppressedRun ω (m+r+1)).j = (allSuppressedRun ω m).j := by
        rcases ht.2 with hs | hd | hu
        · omega
        · omega
        · omega
      refine ⟨?_,?_,?_⟩
      · simpa [Nat.add_assoc] using hnext
      · simpa [Nat.add_assoc] using hj
      · simpa [Nat.add_assoc] using ht.1
  let r := n-m-1
  have hr : m+r < n := by dsimp [r]; omega
  have he : m+r+1 = n := by dsimp [r]; omega
  have hp := hprefix r hr
  have ht := step_walk ω (allSuppressedRun ω (m+r)) hp.2.2
  rw [← next ω (m+r), he] at ht
  refine ⟨?_, ht.1⟩
  rcases ht.2 with hs | hd | hu
  · exfalso; apply hchange; omega
  · left; omega
  · right; omega
