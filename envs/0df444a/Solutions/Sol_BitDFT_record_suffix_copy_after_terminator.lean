-- Prove2me | solution 1 for BitDFT.record_suffix_copy_after_terminator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:23:47.630263+00:00
-- url     : https://prove2.me/submissions/d526b604-347d-4454-8388-d532caa930ae

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
open BitDFT.RecordSuffixCopy IntMul

namespace RSAfterTermAux
open BitDFT.MachineSequence

theorem seq_step_right {M : MultitapeTM} (P Q : Controller M) (c : Q.machine.Cfg) :
    (sequence P Q).machine.step (rightCfg P Q c) = rightCfg P Q (Q.machine.step c) := rfl

theorem seq_iter_right {M : MultitapeTM} (P Q : Controller M) (n : ℕ) (c : Q.machine.Cfg) :
    (sequence P Q).machine.step^[n] (rightCfg P Q c) = rightCfg P Q (Q.machine.step^[n] c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, seq_step_right, ih, Function.iterate_succ_apply]

theorem seq_trans_exit {M : MultitapeTM} (P Q : Controller M) (a : Fin M.k → M.Sym) :
    (sequence P Q).transition (.inl P.exit) a = (.inr Q.entry, fun i => (a i, .stay)) := by
  unfold BitDFT.MachineSequence.sequence
  simp

theorem seq_step_exit {M : MultitapeTM} (P Q : Controller M)
    (cells : Fin M.k → ℕ → M.Sym) (head : Fin M.k → ℕ) :
    (sequence P Q).machine.step (leftCfg P Q ⟨P.exit, cells, head⟩) =
      rightCfg P Q ⟨Q.entry, cells, head⟩ := by
  simp only [MultitapeTM.step, leftCfg, rightCfg, Controller.machine, seq_trans_exit]
  congr 1
  funext i
  simp

theorem seq_step_exit' {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg)
    (hc : c.state = P.exit) :
    (sequence P Q).machine.step (leftCfg P Q c) = rightCfg P Q ⟨Q.entry, c.cells, c.head⟩ := by
  obtain ⟨s, cl, h⟩ := c
  cases hc
  exact seq_step_exit P Q cl h

theorem seq_step_left {M : MultitapeTM} (P Q : Controller M) (c : P.machine.Cfg)
    (h : c.state ≠ P.exit) :
    (sequence P Q).machine.step (leftCfg P Q c) = leftCfg P Q (P.machine.step c) := by
  have ht : ∀ a, (sequence P Q).transition (.inl c.state) a =
      (.inl (P.transition c.state a).1, (P.transition c.state a).2) := by
    intro a
    unfold BitDFT.MachineSequence.sequence
    simp [h]
  simp only [MultitapeTM.step, leftCfg, Controller.machine, ht]

end RSAfterTermAux

namespace RSAfterTermAux
theorem handoff (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    let initial := embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+2]
      (BitDFT.MachineSequence.leftCfg P Q ⟨P.exit,initial.cells,initial.head⟩) =
      BitDFT.MachineSequence.rightCfg P Q
        ⟨(embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).state,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).cells,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).head⟩ := by
  intro P Q initial
  rw [show rest.length + 2 = (rest.length + 1) + 1 from rfl, Function.iterate_succ_apply,
    RSAfterTermAux.seq_step_exit, RSAfterTermAux.seq_iter_right]
  congr 1
  have h := run_embed M cells heads rootCells rootHead
    (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1)) (rest.length+1)
  rw [BitDFT.two_tape_suffix_copy_correct] at h
  have hs : (⟨Q.entry, initial.cells, initial.head⟩ : Q.machine.Cfg) = initial := rfl
  rw [hs]
  exact h

end RSAfterTermAux

theorem solution (M : MultitapeTM)
    (b : (host M).Cfg)
    (hstate : b.state = (host M).qHalt)
    (hblank : b.cells (sourceTape M) (b.head (sourceTape M)) = (host M).blank)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool)
    (hworkspace : Function.update b.cells (sourceTape M)
      (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep) =
        (embed M cells heads rootCells rootHead
          (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).cells)
    (hheads : b.head = (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).head) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+4]
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) =
      BitDFT.MachineSequence.rightCfg P Q
        ⟨(embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).state,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).cells,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).head⟩ := by
  intro P Q
  have hP := BitDFT.record_terminator_sequence_step M b hstate hblank
  have h1 : (BitDFT.MachineSequence.sequence P Q).machine.step
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) =
      BitDFT.MachineSequence.leftCfg P Q (P.machine.step
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) := by
    apply RSAfterTermAux.seq_step_left
    unfold P BitDFT.MachineSequence.sequence
    simp [BitDFT.MachineSequence.leftCfg]
  have e1 : P.machine.step
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b) =
      BitDFT.MachineSequence.rightCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) ⟨false, b.cells, b.head⟩ :=
    RSAfterTermAux.seq_step_exit' (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M) b hstate
  have h2 : (BitDFT.MachineSequence.sequence P Q).machine.step
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.rightCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) ⟨false, b.cells, b.head⟩)) =
      BitDFT.MachineSequence.leftCfg P Q (P.machine.step
        (BitDFT.MachineSequence.rightCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) ⟨false, b.cells, b.head⟩)) := by
    apply RSAfterTermAux.seq_step_left
    unfold P BitDFT.MachineSequence.sequence
    simp [BitDFT.MachineSequence.rightCfg, BitDFT.RecordTerminator.control]
  have h12 : (BitDFT.MachineSequence.sequence P Q).machine.step^[2]
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) =
      BitDFT.MachineSequence.leftCfg P Q (P.machine.step^[2]
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) := by
    rw [Function.iterate_succ_apply, Function.iterate_one, h1, e1, h2,
      Function.iterate_succ_apply, Function.iterate_one, e1]
  rw [show rest.length + 4 = (rest.length + 2) + 2 from rfl, Function.iterate_add_apply, h12]
  have hP' : P.machine.step^[2]
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b) =
      ⟨P.exit, (embed M cells heads rootCells rootHead
          (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).cells,
        (embed M cells heads rootCells rootHead
          (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).head⟩ := by
    rw [← hworkspace, ← hheads]
    exact hP
  rw [hP']
  exact RSAfterTermAux.handoff M cells heads rootCells rootHead base pre rest out
