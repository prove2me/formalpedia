-- Prove2me | solution 1 for BitDFT.coordinate_head_frame_irrelevance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T15:43:14.097008+00:00
-- url     : https://prove2.me/submissions/1f228b1e-b355-477f-a7a7-41d374fc9e32

import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.BankedOperandStageProofSupport BitDFT.MachineSequence
private theorem cfg_ext' {N : MultitapeTM} (P : Controller N)
    (c d : P.machine.Cfg) (hs : c.state = d.state)
    (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem solution {N : MultitapeTM}
    (coord dim out : Fin N.k) (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape)
    (ho : out ≠ N.inTape) (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) (outBits : List N.Sym) (sourceHead outHead head' : ℕ) :
    initialStageFrame coord dim out hc hd ho hcd hco hdo
        ⟨base.state, base.cells, Function.update base.head coord head'⟩ source =
      initialStageFrame coord dim out hc hd ho hcd hco hdo base source ∧
    coordinateCopyFrame coord dim out hc hd ho hcd hco hdo
        ⟨base.state, base.cells, Function.update base.head coord head'⟩
        source outBits sourceHead outHead =
      coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
        source outBits sourceHead outHead := by
  constructor
  · apply cfg_ext' (control N coord dim out hc hd ho hcd hco hdo)
    · rfl
    · rfl
    · funext i
      by_cases hi : i = coord
      · subst i; simp [initialStageFrame]
      · simp [initialStageFrame, Function.update_of_ne hi]
  · apply cfg_ext' (control N coord dim out hc hd ho hcd hco hdo)
    · rfl
    · rfl
    · funext i
      by_cases hi : i = coord
      · subst i; simp [coordinateCopyFrame]
      · simp [coordinateCopyFrame, Function.update_of_ne hi]
end
