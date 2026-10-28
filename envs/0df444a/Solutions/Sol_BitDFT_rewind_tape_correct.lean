-- Prove2me | solution 1 for BitDFT.rewind_tape_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:10:19.404795+00:00
-- url     : https://prove2.me/submissions/370177e4-276f-4c9d-be0f-8b3c3bcff809

import Definitions.Def_BitDFT_RewindTape
import Mathlib.Tactic
namespace BitDFT.RewindTape
open IntMul
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem left_step (N : MultitapeTM) (j : Fin N.k) (base : N.Cfg) (p : ℕ)
    (hn : base.cells j (p+1) ≠ N.startSym) :
    (machine N j).step (frame N j base false (p+1)) = frame N j base false p := by
  apply cfg_ext
  · simp [MultitapeTM.step,frame,control,transition,hn]
  · funext i
    change Function.update (base.cells i) _ (base.cells i _) = base.cells i
    exact Function.update_eq_self _ _
  · funext i
    by_cases hij : i = j
    · subst i
      simp [MultitapeTM.step,frame,control,transition,hn]
    · simp [MultitapeTM.step,frame,control,transition,hn,hij]

theorem zero_step (N : MultitapeTM) (j : Fin N.k) (base : N.Cfg)
    (hz : base.cells j 0 = N.startSym) :
    (machine N j).step (frame N j base false 0) = frame N j base true 1 := by
  apply cfg_ext
  · simp [MultitapeTM.step,frame,control,transition,hz]
  · funext i
    change Function.update (base.cells i) _ (base.cells i _) = base.cells i
    exact Function.update_eq_self _ _
  · funext i
    by_cases hij : i = j
    · subst i
      simp [MultitapeTM.step,frame,control,transition,hz]
    · simp [MultitapeTM.step,frame,control,transition,hz,hij]

theorem left_run (N : MultitapeTM) (j : Fin N.k) (base : N.Cfg)
    (hn : ∀ p, 0 < p → base.cells j p ≠ N.startSym) (p : ℕ) :
    (machine N j).step^[p] (frame N j base false p) = frame N j base false 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,left_step N j base p (hn _ (by omega)),ih]
end BitDFT.RewindTape
open BitDFT.RewindTape IntMul

theorem solution (N : MultitapeTM) (j : Fin N.k) (base : N.Cfg)
    (hz : base.cells j 0 = N.startSym)
    (hn : ∀ p, 0 < p → base.cells j p ≠ N.startSym) (p : ℕ) :
    (machine N j).step^[p+1] (frame N j base false p) = frame N j base true 1 := by
  rw [Function.iterate_succ_apply',left_run N j base hn p,zero_step N j base hz]
