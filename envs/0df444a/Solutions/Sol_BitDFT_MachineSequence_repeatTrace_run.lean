-- Prove2me | solution 1 for BitDFT.MachineSequence.repeatTrace_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T03:15:37.981229+00:00
-- url     : https://prove2.me/submissions/6869d9f8-4d67-4d61-bf7d-1e529cc20c3b

import Definitions.Def_BitDFT_RepeatUntilBlank

set_option autoImplicit false

namespace BitDFT.MachineSequence
open IntMul

/-- Until the body first reaches its exit, the repeated controller agrees
step-for-step with that body. -/
theorem repeatBody_run {M : MultitapeTM} (P : Controller M)
    (c : P.machine.Cfg) (t : ℕ)
    (hfirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit) :
    (repeatMachine P).step^[t] (repeatBodyCfg c) =
      repeatBodyCfg (P.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hsub : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit := by
      intro s hs
      exact hfirst s (by omega)
    have hstate : (P.machine.step^[t] c).state ≠ P.exit := hfirst t (by omega)
    calc
      (repeatMachine P).step^[(t + 1)] (repeatBodyCfg c) =
          (repeatMachine P).step ((repeatMachine P).step^[t] (repeatBodyCfg c)) := by
            rw [Function.iterate_succ_apply']
      _ = (repeatMachine P).step (repeatBodyCfg (P.machine.step^[t] c)) := by rw [ih hsub]
      _ = repeatBodyCfg (P.machine.step (P.machine.step^[t] c)) :=
            repeatBody_step P _ hstate
      _ = repeatBodyCfg (P.machine.step^[(t + 1)] c) := by
            rw [Function.iterate_succ_apply']

/-- A sequence of body runs certified by `RepeatTrace` executes as one fixed
machine run; the trace length counts every body step and one loop-control step
per source record, including the final blank test. -/
theorem repeatTrace_run {M : MultitapeTM} (P : Controller M)
    {t : ℕ} {c : P.machine.Cfg} {final : (repeatMachine P).Cfg}
    (h : RepeatTrace P t c final) :
    (repeatMachine P).step^[t] (repeatBodyCfg c) = final := by
  classical
  induction h with
  | @stop c0 hExit hBlank =>
    calc
      (repeatMachine P).step^[1] (repeatBodyCfg c0) =
          (repeatMachine P).step (repeatBodyCfg c0) := by simp
      _ = repeatHaltCfg P c0 := by
          rw [repeatBody_exit_step P c0 hExit]
          simp [hBlank, repeatHaltCfg]
  | @next t m c d final hEntry hRun hFirst hExit hNonblank hTail ih =>
    have hbody := repeatBody_run P c t hFirst
    have hresume : (repeatMachine P).step (repeatBodyCfg d) =
        repeatBodyCfg (repeatBodyEntryCfg P d) := by
      rw [repeatBody_exit_step P d hExit]
      simp [hNonblank, repeatBodyCfg, repeatBodyEntryCfg]
    calc
      (repeatMachine P).step^[(t + 1 + m)] (repeatBodyCfg c) =
          (repeatMachine P).step^[m]
            ((repeatMachine P).step^[(t + 1)] (repeatBodyCfg c)) := by
              rw [show t + 1 + m = m + (t + 1) by omega, Function.iterate_add_apply]
      _ = (repeatMachine P).step^[m]
            ((repeatMachine P).step ((repeatMachine P).step^[t] (repeatBodyCfg c))) := by
              rw [Function.iterate_succ_apply']
      _ = (repeatMachine P).step^[m] (repeatBodyCfg (repeatBodyEntryCfg P d)) := by
              rw [hbody, hRun, hresume]
      _ = final := ih

end BitDFT.MachineSequence

theorem solution {M : IntMul.MultitapeTM}
    (P : BitDFT.MachineSequence.Controller M) {t : ℕ}
    {c : P.machine.Cfg} {final : (BitDFT.MachineSequence.repeatMachine P).Cfg}
    (h : BitDFT.MachineSequence.RepeatTrace P t c final) :
    (BitDFT.MachineSequence.repeatMachine P).step^[t]
      (BitDFT.MachineSequence.repeatBodyCfg c) = final :=
  BitDFT.MachineSequence.repeatTrace_run P h
