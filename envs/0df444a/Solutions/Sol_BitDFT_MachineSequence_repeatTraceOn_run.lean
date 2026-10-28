-- Prove2me | solution 1 for BitDFT.MachineSequence.repeatTraceOn_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T03:29:43.362459+00:00
-- url     : https://prove2.me/submissions/474932a6-0681-437d-b1b5-149350312494

import Definitions.Def_BitDFT_RepeatUntilBlankOn
import Mathlib.Tactic

set_option autoImplicit false
open IntMul
namespace BitDFT.MachineSequence
/-- Until the body first reaches its exit, the repeated controller agrees
step-for-step with that body. -/
private theorem repeatBodyOn_run {M : MultitapeTM} (source : Fin M.k) (P : Controller M)
    (c : P.machine.Cfg) (t : ℕ)
    (hfirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit) :
    (repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c) =
      repeatBodyCfgOn source (P.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hsub : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit := by
      intro s hs
      exact hfirst s (by omega)
    have hstate : (P.machine.step^[t] c).state ≠ P.exit := hfirst t (by omega)
    calc
      (repeatMachineOn source P).step^[(t + 1)] (repeatBodyCfgOn source c) =
          (repeatMachineOn source P).step ((repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c)) := by
            rw [Function.iterate_succ_apply']
      _ = (repeatMachineOn source P).step (repeatBodyCfgOn source (P.machine.step^[t] c)) := by rw [ih hsub]
      _ = repeatBodyCfgOn source (P.machine.step (P.machine.step^[t] c)) :=
            repeatBodyOn_step source P _ hstate
      _ = repeatBodyCfgOn source (P.machine.step^[(t + 1)] c) := by
            rw [Function.iterate_succ_apply']

/-- A sequence of body runs certified by `RepeatTraceOn` executes as one fixed
machine run; the trace length counts every body step and one loop-control step
per source record, including the final blank test. -/
theorem repeatTraceOn_run_local {M : MultitapeTM} (source : Fin M.k) (P : Controller M)
    {t : ℕ} {c : P.machine.Cfg} {final : (repeatMachineOn source P).Cfg}
    (h : RepeatTraceOn source P t c final) :
    (repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c) = final := by
  classical
  induction h with
  | @stop c0 hExit hBlank =>
    calc
      (repeatMachineOn source P).step^[1] (repeatBodyCfgOn source c0) =
          (repeatMachineOn source P).step (repeatBodyCfgOn source c0) := by simp
      _ = repeatHaltCfgOn source P c0 := by
          rw [repeatBodyOn_exit_step P source c0 hExit]
          simp [hBlank, repeatHaltCfgOn]
  | @next t m c d final hEntry hRun hFirst hExit hNonblank hTail ih =>
    have hbody := repeatBodyOn_run source P c t hFirst
    have hresume : (repeatMachineOn source P).step (repeatBodyCfgOn source d) =
        repeatBodyCfgOn source (repeatBodyEntryCfgOn source P d) := by
      rw [repeatBodyOn_exit_step P source d hExit]
      simp [hNonblank, repeatBodyCfgOn, repeatBodyEntryCfgOn]
    calc
      (repeatMachineOn source P).step^[(t + 1 + m)] (repeatBodyCfgOn source c) =
          (repeatMachineOn source P).step^[m]
            ((repeatMachineOn source P).step^[(t + 1)] (repeatBodyCfgOn source c)) := by
              rw [show t + 1 + m = m + (t + 1) by omega, Function.iterate_add_apply]
      _ = (repeatMachineOn source P).step^[m]
            ((repeatMachineOn source P).step ((repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c))) := by
              rw [Function.iterate_succ_apply']
      _ = (repeatMachineOn source P).step^[m] (repeatBodyCfgOn source (repeatBodyEntryCfgOn source P d)) := by
              rw [hbody, hRun, hresume]
      _ = final := ih

end BitDFT.MachineSequence

theorem solution {M : IntMul.MultitapeTM} (source : Fin M.k)
    (P : BitDFT.MachineSequence.Controller M) {t : ℕ}
    {c : P.machine.Cfg} {final : (BitDFT.MachineSequence.repeatMachineOn source P).Cfg}
    (h : BitDFT.MachineSequence.RepeatTraceOn source P t c final) :
    (BitDFT.MachineSequence.repeatMachineOn source P).step^[t]
      (BitDFT.MachineSequence.repeatBodyCfgOn source c) = final :=
  BitDFT.MachineSequence.repeatTraceOn_run_local source P h
