-- Prove2me | solution 1 for BitDFT.machine_sequence_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:22:59.522635+00:00
-- url     : https://prove2.me/submissions/6788a4f1-5399-4b34-ba44-03190930f57a

import Definitions.Def_BitDFT_MachineSequence
namespace BitDFT.MachineSequence
open IntMul

theorem step_left {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg)
    (h : c.state ≠ P.exit) :
    (sequence P Q).machine.step (leftCfg P Q c) = leftCfg P Q (P.machine.step c) := by
  simp [MultitapeTM.step, leftCfg, sequence, h]

theorem step_right {M : MultitapeTM} (P Q : Controller M) (c : Q.machine.Cfg) :
    (sequence P Q).machine.step (rightCfg P Q c) = rightCfg P Q (Q.machine.step c) := by
  rfl

theorem step_handoff {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg)
    (h : c.state = P.exit) :
    (sequence P Q).machine.step (leftCfg P Q c) = rightCfg P Q (handoff P Q c) := by
  simp [MultitapeTM.step, leftCfg, rightCfg, handoff, sequence, h]

theorem run_left {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg)
    (t : ℕ) (h : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit) :
    (sequence P Q).machine.step^[t] (leftCfg P Q c) =
      leftCfg P Q (P.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by intro s hs; exact h s (by omega))]
    rw [step_left P Q _ (h t (by omega)), Function.iterate_succ_apply']

theorem run_right {M : MultitapeTM} (P Q : Controller M) (c : Q.machine.Cfg)
    (t : ℕ) :
    (sequence P Q).machine.step^[t] (rightCfg P Q c) =
      rightCfg P Q (Q.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, step_right, Function.iterate_succ_apply']

/-- Exact sequential execution, including the single transition needed to dispatch Q. -/
theorem run_sequence {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg)
    (t u : ℕ) (h : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit)
    (ht : (P.machine.step^[t] c).state = P.exit) :
    (sequence P Q).machine.step^[t + 1 + u] (leftCfg P Q c) =
      rightCfg P Q (Q.machine.step^[u] (handoff P Q (P.machine.step^[t] c))) := by
  rw [show t + 1 + u = u + (t + 1) by omega, Function.iterate_add_apply,
    Function.iterate_succ_apply', run_left P Q c t h, step_handoff P Q _ ht, run_right]

private theorem frozen_step {M : MultitapeTM} (P : Controller M) (c : P.machine.Cfg)
    (h : c.state = P.exit) : P.machine.step c = c := by
  cases c
  simp_all [MultitapeTM.step, Controller.machine, P.frozen]

private theorem frozen_run {M : MultitapeTM} (P : Controller M) (c : P.machine.Cfg)
    (h : c.state = P.exit) (t : ℕ) : P.machine.step^[t] c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, frozen_step P c h]

end BitDFT.MachineSequence

open BitDFT.MachineSequence IntMul

/-- An upper bound on the first stage suffices: padded halting runs do not delay handoff. -/
theorem solution {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg)
    (t u : ℕ) (ht : (P.machine.step^[t] c).state = P.exit) :
    ∃ v ≤ t + 1 + u,
      (sequence P Q).machine.step^[v] (leftCfg P Q c) =
        rightCfg P Q (Q.machine.step^[u] (handoff P Q (P.machine.step^[t] c))) := by
  classical
  have hex : ∃ s, (P.machine.step^[s] c).state = P.exit := ⟨t, ht⟩
  let s := Nat.find hex
  have hs : (P.machine.step^[s] c).state = P.exit := Nat.find_spec hex
  have hst : s ≤ t := Nat.find_min' hex ht
  have hbefore : ∀ r < s, (P.machine.step^[r] c).state ≠ P.exit := by
    intro r hr he
    have := Nat.find_min' hex he
    omega
  have heq : P.machine.step^[t] c = P.machine.step^[s] c := by
    rw [show t = (t-s)+s by omega, Function.iterate_add_apply]
    exact frozen_run P _ hs _
  refine ⟨s+1+u, by omega, ?_⟩
  rw [heq]
  exact run_sequence P Q c s u hbefore hs

