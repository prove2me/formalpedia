-- Prove2me | solution 1 for BitDFT.counted_block_reentry_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:02:36.821173+00:00
-- url     : https://prove2.me/submissions/108e9574-20e7-4065-982c-ce528fd4af53

import Definitions.Def_BitDFT_CountedBlock
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

set_option autoImplicit false
open IntMul

private theorem cfg_ext (c d : IntMul.CountedStream.machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

/-- After one counted block, the source and destination heads are already at
    the next block boundary; the countdown/template tapes are reset, so the
    same copier can be re-entered on the remaining suffix. -/
theorem solution (pre out x y : List Bool)
    (hx : IntMul.val y + 1 ≤ x.length) :
    let m := IntMul.val y + 1
    (⟨.emit,
      (BitDFT.CountedBlock.frame pre out x y y.reverse m .halt).cells,
      (BitDFT.CountedBlock.frame pre out x y y.reverse m .halt).head⟩ :
        IntMul.CountedStream.machine.Cfg) =
      BitDFT.CountedBlock.frame (pre ++ x.take m) (out ++ x.take m)
        (x.drop m) y y.reverse 0 .emit := by
  dsimp only
  let m := IntMul.val y + 1
  have htake : (x.take m).length = m := List.length_take_of_le hx
  have hsplit := List.take_append_drop m x
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [BitDFT.CountedBlock.frame, IntMul.CountedStream.machine, hsplit,
        htake, List.map_append, List.take_zero]
  · funext i
    fin_cases i <;>
      simp [BitDFT.CountedBlock.frame, htake, List.length_append, Nat.add_assoc]
    all_goals omega
