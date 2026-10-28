-- Prove2me | solution 1 for BitDFT.OperandStage.run_preserves_other_tape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T17:48:37.002607+00:00
-- url     : https://prove2.me/submissions/5172b1fc-ecdf-4161-ad4e-edc5a363b1c4

import Definitions.Def_BitDFT_OperandStage
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace BitDFT.OperandStage
open IntMul

theorem step_preserves_other_tape {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (i : Fin N.k) (hic : i ≠ coord) (hid : i ≠ dim) (hio : i ≠ out) :
    ((control N coord dim out hc hd ho hcd hco hdo).machine.step c).cells i = c.cells i ∧
    ((control N coord dim out hc hd ho hcd hco hdo).machine.step c).head i = c.head i := by
  let a : Fin N.k → N.Sym := fun j => c.cells j (c.head j)
  have hraw : (raw N coord dim out c.state a).2 i = (a i, Move.stay) := by
    cases c.state <;> simp [raw, a, hic, hid, hio] <;> split_ifs <;> simp [hic, hid, hio]
  have hwrite : (transition N coord dim out c.state a).2 i = (a i, Move.stay) := by
    dsimp [transition]
    rw [hraw]
    by_cases hs : a i = N.startSym <;> simp [protect, hs]
  change Function.update (c.cells i) (c.head i)
      (((transition N coord dim out c.state a).2 i).1) = c.cells i ∧
    (match ((transition N coord dim out c.state a).2 i).2 with
      | Move.left => c.head i - 1
      | Move.stay => c.head i
      | Move.right => c.head i + 1) = c.head i
  rw [hwrite]
  constructor
  · simp [a]
  · rfl

theorem solution {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (i : Fin N.k) (hic : i ≠ coord) (hid : i ≠ dim) (hio : i ≠ out) (t : ℕ) :
    ((control N coord dim out hc hd ho hcd hco hdo).machine.step^[t] c).cells i = c.cells i ∧
    ((control N coord dim out hc hd ho hcd hco hdo).machine.step^[t] c).head i = c.head i := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hcells, hhead⟩ := ih
      have hstep := step_preserves_other_tape coord dim out hc hd ho hcd hco hdo
        ((control N coord dim out hc hd ho hcd hco hdo).machine.step^[t] c) i hic hid hio
      rw [hcells, hhead] at hstep
      exact hstep

end BitDFT.OperandStage
end

abbrev solution := @BitDFT.OperandStage.solution
