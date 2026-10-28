-- Prove2me | solution 1 for BitDFT.repeatTraceOnBounded_runtime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T20:30:43.242336+00:00
-- url     : https://prove2.me/submissions/39997130-78e9-449a-8184-3ea18149a4f5

import Definitions.Def_BitDFT_RepeatTraceOnBounded
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace BitDFT.MachineSequence
open IntMul

theorem repeatBodyOn_run_local {M : MultitapeTM} (source : Fin M.k)
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
          (repeatMachineOn source P).step ((repeatMachineOn source P).step^[t]
            (repeatBodyCfgOn source c)) := by rw [Function.iterate_succ_apply']
      _ = (repeatMachineOn source P).step
            (repeatBodyCfgOn source (P.machine.step^[t] c)) := by rw [ih hsub]
      _ = repeatBodyCfgOn source (P.machine.step (P.machine.step^[t] c)) :=
            repeatBodyOn_step source P _ hstate
      _ = repeatBodyCfgOn source (P.machine.step^[(t + 1)] c) := by
            rw [Function.iterate_succ_apply']

theorem repeatTraceOn_run_local {M : MultitapeTM} (source : Fin M.k)
    (P : Controller M) {t : ℕ} {c : P.machine.Cfg}
    {final : (repeatMachineOn source P).Cfg}
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
  | @next t m c0 d final hEntry hRun hFirst hExit hNonblank hTail ih =>
    have hbody := repeatBodyOn_run_local source P c0 t hFirst
    have hresume : (repeatMachineOn source P).step (repeatBodyCfgOn source d) =
        repeatBodyCfgOn source (repeatBodyEntryCfgOn source P d) := by
      rw [repeatBodyOn_exit_step P source d hExit]
      simp [hNonblank, repeatBodyCfgOn, repeatBodyEntryCfgOn]
    calc
      (repeatMachineOn source P).step^[(t + 1 + m)] (repeatBodyCfgOn source c0) =
          (repeatMachineOn source P).step^[m]
            ((repeatMachineOn source P).step^[(t + 1)] (repeatBodyCfgOn source c0)) := by
              rw [show t + 1 + m = m + (t + 1) by omega, Function.iterate_add_apply]
      _ = (repeatMachineOn source P).step^[m]
            ((repeatMachineOn source P).step ((repeatMachineOn source P).step^[t]
              (repeatBodyCfgOn source c0))) := by rw [Function.iterate_succ_apply']
      _ = (repeatMachineOn source P).step^[m]
            (repeatBodyCfgOn source (repeatBodyEntryCfgOn source P d)) := by
              rw [hbody, hRun, hresume]
      _ = final := ih

/-- If each body run costs at most `B`, and the trace has `r` rounds (including
its final blank test), the full repeated machine costs at most `r*(B+1)`. -/
theorem repeatTraceOnBounded_time {M : MultitapeTM} (source : Fin M.k)
    (P : Controller M) (B t : ℕ) (c : P.machine.Cfg)
    (final : (repeatMachineOn source P).Cfg)
    (h : RepeatTraceOnBounded source P B t c final) :
    t ≤ repeatTraceOnBoundedRounds h * (B + 1) := by
  induction h with
  | stop hExit hBlank => simp [repeatTraceOnBoundedRounds]
  | @next t0 m c0 d final0 hEntry hRun hFirst hExit hNonblank hBodyBound hTail ih =>
    change t0 + 1 + m ≤ (repeatTraceOnBoundedRounds hTail + 1) * (B + 1)
    calc
      t0 + 1 + m ≤ (B + 1) + m := by omega
      _ ≤ (B + 1) + repeatTraceOnBoundedRounds hTail * (B + 1) :=
        Nat.add_le_add_left ih _
      _ = (repeatTraceOnBoundedRounds hTail + 1) * (B + 1) := by
        calc
          (B + 1) + repeatTraceOnBoundedRounds hTail * (B + 1) =
              repeatTraceOnBoundedRounds hTail * (B + 1) + (B + 1) := Nat.add_comm _ _
          _ = (repeatTraceOnBoundedRounds hTail + 1) * (B + 1) := by
            rw [Nat.add_mul]
            simp

theorem repeatTraceOnBounded_runtime {M : MultitapeTM} (source : Fin M.k)
    (P : Controller M) (B t : ℕ) (c : P.machine.Cfg)
    (final : (repeatMachineOn source P).Cfg)
    (h : RepeatTraceOnBounded source P B t c final) :
    (repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c) = final ∧
      t ≤ repeatTraceOnBoundedRounds h * (B + 1) := by
  exact ⟨repeatTraceOn_run_local source P h.toTrace,
    repeatTraceOnBounded_time source P B t c final h⟩

end BitDFT.MachineSequence

theorem solution {M : IntMul.MultitapeTM} (source : Fin M.k)
    (P : BitDFT.MachineSequence.Controller M) (B t : ℕ)
    (c : P.machine.Cfg) (final : (BitDFT.MachineSequence.repeatMachineOn source P).Cfg)
    (h : BitDFT.MachineSequence.RepeatTraceOnBounded source P B t c final) :
    (BitDFT.MachineSequence.repeatMachineOn source P).step^[t]
        (BitDFT.MachineSequence.repeatBodyCfgOn source c) = final ∧
      t ≤ BitDFT.MachineSequence.repeatTraceOnBoundedRounds h * (B + 1) :=
  BitDFT.MachineSequence.repeatTraceOnBounded_runtime source P B t c final h
