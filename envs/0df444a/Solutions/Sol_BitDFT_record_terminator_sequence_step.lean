-- Prove2me | solution 1 for BitDFT.record_terminator_sequence_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:38:03.35946+00:00
-- url     : https://prove2.me/submissions/ed75d606-835d-45a2-ad2e-13a0ce618310

import Definitions.Def_BitDFT_RecordTerminator
open IntMul BitDFT.MachineSequence BitDFT.RecordTerminator

private theorem cfg_ext {N : MultitapeTM} (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem handoff_step {N : MultitapeTM} (P Q : Controller N)
    (c : P.machine.Cfg) (h : c.state = P.exit) :
    (sequence P Q).machine.step (leftCfg P Q c) = rightCfg P Q (handoff P Q c) := by
  apply cfg_ext
  · simp [MultitapeTM.step, BitDFT.MachineSequence.sequence, leftCfg, rightCfg, handoff, h]
  · funext i
    simp [MultitapeTM.step, BitDFT.MachineSequence.sequence, leftCfg, rightCfg, handoff, h]
  · funext i
    simp [MultitapeTM.step, BitDFT.MachineSequence.sequence, leftCfg, rightCfg, handoff, h]

private theorem right_step {N : MultitapeTM} (P Q : Controller N)
    (c : Q.machine.Cfg) :
    (sequence P Q).machine.step (rightCfg P Q c) = rightCfg P Q (Q.machine.step c) := by
  apply cfg_ext
  · simp [MultitapeTM.step, BitDFT.MachineSequence.sequence, rightCfg]
  · funext i
    simp [MultitapeTM.step, BitDFT.MachineSequence.sequence, rightCfg]
  · funext i
    simp [MultitapeTM.step, BitDFT.MachineSequence.sequence, rightCfg]

theorem solution (M : MultitapeTM) (b : (storage M).Cfg)
    (hstate : b.state = (storage M).qHalt)
    (hblank : b.cells (target M) (b.head (target M)) = (storage M).blank) :
    (machine M).step^[2] (leftCfg (native (storage M)) (control M) b) =
      rightCfg (native (storage M)) (control M)
        ⟨true, Function.update b.cells (target M)
          (Function.update (b.cells (target M)) (b.head (target M)) (storage M).sep), b.head⟩ := by
  have h1 := handoff_step (native (storage M)) (control M) b hstate
  have h2 := right_step (native (storage M)) (control M)
    (handoff (native (storage M)) (control M) b)
  calc
    (machine M).step^[2] (leftCfg (native (storage M)) (control M) b) =
        (machine M).step ((machine M).step (leftCfg (native (storage M)) (control M) b)) := by
          norm_num [Function.iterate_succ_apply']
    _ = (machine M).step (rightCfg (native (storage M)) (control M)
          (handoff (native (storage M)) (control M) b)) := by rw [h1]
    _ = rightCfg (native (storage M)) (control M)
          ((controlMachine M).step (handoff (native (storage M)) (control M) b)) := h2
    _ = rightCfg (native (storage M)) (control M)
          ⟨true, Function.update b.cells (target M)
            (Function.update (b.cells (target M)) (b.head (target M)) (storage M).sep), b.head⟩ := by
          rw [show handoff (native (storage M)) (control M) b =
            ⟨false,b.cells,b.head⟩ by rfl]
          rw [control_step M b.cells b.head hblank]
