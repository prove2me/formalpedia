-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.full_suppressed_walk_step
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:47:17.151304+00:00
-- url     : https://prove2.me/submissions/dbff3485-c198-496e-80a0-7bf08e79a8e4

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private def WalkPhase : Phase → Prop
  | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
  | .uniformCheck | .done _ => True
  | _ => False

/-- Once initialized, a suppressed step stays in the walk phase and is either
silent, a decrease by one, or an increase by (2,1). -/
theorem solution (ω : Entropy) (s : State) (hs : (match s.phase with
    | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
    | .uniformCheck | .done _ => True | _ => False)) :
    (match (allSuppressedStep ω s).phase with
    | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
    | .uniformCheck | .done _ => True | _ => False) ∧
    (((allSuppressedStep ω s).i = s.i ∧ (allSuppressedStep ω s).j = s.j) ∨
     ((allSuppressedStep ω s).i = s.i - 1 ∧ (allSuppressedStep ω s).j = s.j) ∨
     ((allSuppressedStep ω s).i = s.i + 2 ∧ (allSuppressedStep ω s).j = s.j + 1)) := by
  change WalkPhase s.phase at hs
  change WalkPhase (allSuppressedStep ω s).phase ∧ _
  cases hp : s.phase with
  | start => simp [WalkPhase, hp] at hs
  | initialCheck => simp [WalkPhase, hp] at hs
  | loop =>
    simp only [allSuppressedStep, suppressedStep, step, hp]
    split <;> simp [WalkPhase]
  | coinOracle k =>
    cases k with
    | initial => simp [WalkPhase,hp] at hs
    | first =>
      simp only [allSuppressedStep, suppressedStep, step, hp]
      split <;> simp [coinReturn,WalkPhase]
    | second =>
      simp only [allSuppressedStep, suppressedStep, step, hp]
      split <;> simp [coinReturn,WalkPhase]
  | coinFair k =>
    cases k with
    | initial => simp [WalkPhase,hp] at hs
    | first =>
      simp only [allSuppressedStep, suppressedStep, step, hp]
      split <;> simp [coinReturn,WalkPhase]
    | second =>
      simp only [allSuppressedStep, suppressedStep, step, hp]
      split <;> simp [coinReturn,WalkPhase]
  | uniformCheck => simp [allSuppressedStep,suppressedStep,hp,WalkPhase]
  | done b => simp [allSuppressedStep,suppressedStep,step,hp,WalkPhase]
