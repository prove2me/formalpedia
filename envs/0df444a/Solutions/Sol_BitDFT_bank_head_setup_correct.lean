-- Prove2me | solution 1 for BitDFT.bank_head_setup_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:21:32.657888+00:00
-- url     : https://prove2.me/submissions/51c8f543-4b1a-4da1-b58f-dd0333433ce5

import Definitions.Def_BitDFT_BankHeadSetup

namespace BitDFT.BankHeadSetup
open IntMul
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem setup_step (N : MultitapeTM) (r : ℕ) (base : N.Cfg) :
    (machine N r).step (start N r base) = finish N r base := by
  apply cfg_ext
  · rfl
  · funext i
    exact Function.update_eq_self _ _
  · funext i
    by_cases hi : selected r i.val <;> simp [MultitapeTM.step,start,finish,control,transition,hi]

end BitDFT.BankHeadSetup
open BitDFT.BankHeadSetup IntMul

theorem solution (N : MultitapeTM) (r : ℕ) (base : N.Cfg) :
    (machine N r).step (start N r base) = finish N r base ∧
    (finish N r base).cells = base.cells ∧
    (∀ i : Fin N.k, 2 ≤ i.val → i.val < r+2 → base.head i = 0 → (finish N r base).head i = 1) ∧
    (finish N r base).head N.inTape = base.head N.inTape ∧
    (finish N r base).head N.outTape = base.head N.outTape := by
  refine ⟨setup_step N r base,rfl,?_,?_,?_⟩
  · intro i hlo hhi hz
    simp [finish,selected,hlo,hhi,hz]
  · simp [finish,selected,MultitapeTM.inTape]
  · simp [finish,selected,MultitapeTM.outTape]
