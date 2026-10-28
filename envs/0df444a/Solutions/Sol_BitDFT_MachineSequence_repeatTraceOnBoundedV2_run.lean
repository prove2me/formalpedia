-- Prove2me | solution 1 for BitDFT.MachineSequence.repeatTraceOnBoundedV2_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T23:00:24.380683+00:00
-- url     : https://prove2.me/submissions/357c1dda-d3eb-4544-b875-e8dddb630c9a

import Definitions.Def_BitDFT_RepeatTraceOnBoundedV2
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace BitDFT.MachineSequence
open IntMul

private theorem repeatBodyOn_run_v2 {M : MultitapeTM} (source : Fin M.k)
    (P : Controller M) (c : P.machine.Cfg) (t : ℕ)
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
          (repeatMachineOn source P).step
            ((repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c)) := by
              rw [Function.iterate_succ_apply']
      _ = (repeatMachineOn source P).step
            (repeatBodyCfgOn source (P.machine.step^[t] c)) := by rw [ih hsub]
      _ = repeatBodyCfgOn source (P.machine.step (P.machine.step^[t] c)) :=
            repeatBodyOn_step source P _ hstate
      _ = repeatBodyCfgOn source (P.machine.step^[(t + 1)] c) := by
            rw [Function.iterate_succ_apply']

theorem repeatTraceOnBoundedV2_run {M : MultitapeTM} (source : Fin M.k)
    (P : Controller M) {B t : ℕ} {c : P.machine.Cfg}
    {final : (repeatMachineOn source P).Cfg}
    (h : RepeatTraceOnBoundedV2 source P B t c final) :
    (repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c) = final ∧
      t ≤ repeatTraceOnBoundedV2Rounds h * (B + 1) := by
  classical
  induction h with
  | @last t c d hEntry hRun hFirst hExit hBlank hBodyBound =>
    have hbody := repeatBodyOn_run_v2 source P c t hFirst
    constructor
    · calc
        (repeatMachineOn source P).step^[(t + 1)] (repeatBodyCfgOn source c) =
            (repeatMachineOn source P).step
              ((repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c)) := by
                rw [Function.iterate_succ_apply']
        _ = (repeatMachineOn source P).step (repeatBodyCfgOn source d) := by
              rw [hbody, hRun]
        _ = repeatHaltCfgOn source P d := by
              rw [repeatBodyOn_exit_step P source d hExit]
              simp [hBlank, repeatHaltCfgOn]
    · simp [repeatTraceOnBoundedV2Rounds]
      omega
  | @next t m c d final hEntry hRun hFirst hExit hNonblank hBodyBound hTail ih =>
    have hbody := repeatBodyOn_run_v2 source P c t hFirst
    have hresume : (repeatMachineOn source P).step (repeatBodyCfgOn source d) =
        repeatBodyCfgOn source (repeatBodyEntryCfgOn source P d) := by
      rw [repeatBodyOn_exit_step P source d hExit]
      simp [hNonblank, repeatBodyCfgOn, repeatBodyEntryCfgOn]
    constructor
    · calc
        (repeatMachineOn source P).step^[(t + 1 + m)] (repeatBodyCfgOn source c) =
            (repeatMachineOn source P).step^[m]
              ((repeatMachineOn source P).step^[(t + 1)] (repeatBodyCfgOn source c)) := by
                rw [show t + 1 + m = m + (t + 1) by omega, Function.iterate_add_apply]
        _ = (repeatMachineOn source P).step^[m]
              ((repeatMachineOn source P).step
                ((repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c))) := by
                  rw [Function.iterate_succ_apply']
        _ = (repeatMachineOn source P).step^[m]
              (repeatBodyCfgOn source (repeatBodyEntryCfgOn source P d)) := by
                rw [hbody, hRun, hresume]
        _ = final := ih.1
    · change t + 1 + m ≤
        (repeatTraceOnBoundedV2Rounds hTail + 1) * (B + 1)
      calc
        t + 1 + m ≤ (B + 1) + m := by omega
        _ ≤ (B + 1) + repeatTraceOnBoundedV2Rounds hTail * (B + 1) :=
          Nat.add_le_add_left ih.2 _
        _ = (repeatTraceOnBoundedV2Rounds hTail + 1) * (B + 1) := by
          rw [Nat.add_mul]
          omega

end BitDFT.MachineSequence

theorem solution {M : IntMul.MultitapeTM} (source : Fin M.k)
    (P : BitDFT.MachineSequence.Controller M) (B t : ℕ)
    (c : P.machine.Cfg) (final : (BitDFT.MachineSequence.repeatMachineOn source P).Cfg)
    (h : BitDFT.MachineSequence.RepeatTraceOnBoundedV2 source P B t c final) :
    (BitDFT.MachineSequence.repeatMachineOn source P).step^[t]
        (BitDFT.MachineSequence.repeatBodyCfgOn source c) = final ∧
      t ≤ BitDFT.MachineSequence.repeatTraceOnBoundedV2Rounds h * (B + 1) :=
  BitDFT.MachineSequence.repeatTraceOnBoundedV2_run source P h
