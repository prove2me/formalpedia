-- Prove2me | solution 1 for BitDFT.record_suffix_copy_handoff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:23:39.386599+00:00
-- url     : https://prove2.me/submissions/92fa4d4c-78e3-40e6-bd49-c7d664b50965

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
open BitDFT.RecordSuffixCopy IntMul

namespace RSHandoffAux
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

end RSHandoffAux

theorem solution (M : MultitapeTM)
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
    RSHandoffAux.seq_step_exit, RSHandoffAux.seq_iter_right]
  congr 1
  have h := run_embed M cells heads rootCells rootHead
    (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1)) (rest.length+1)
  rw [BitDFT.two_tape_suffix_copy_correct] at h
  have hs : (⟨Q.entry, initial.cells, initial.head⟩ : Q.machine.Cfg) = initial := rfl
  rw [hs]
  exact h
