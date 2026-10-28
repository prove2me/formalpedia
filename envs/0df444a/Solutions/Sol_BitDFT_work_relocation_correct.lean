-- Prove2me | solution 1 for BitDFT.work_relocation_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:56:47.228883+00:00
-- url     : https://prove2.me/submissions/ba8835de-1569-45ee-8dd5-f113df0d0b1f

import Definitions.Def_BitDFT_WorkRelocation

namespace BitDFT.WorkRelocation
open IntMul
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem step_embed (M : MultitapeTM) (rootCells : ℕ → M.Sym) (rootHead : ℕ) (c : M.Cfg) :
    (machine M).step (embed M rootCells rootHead c) = embed M rootCells rootHead (M.step c) := by
  have hr : (fun j => (embed M rootCells rootHead c).cells (oldTape M j)
      ((embed M rootCells rootHead c).head (oldTape M j))) = (fun j => c.cells j (c.head j)) := by
    funext j
    simp [embed,oldTape,innerTape]
  apply cfg_ext
  · change (M.δ c.state _).1 = (M.δ c.state _).1
    rw [hr]
  · funext i
    by_cases hi : i = 0
    · subst i
      simp [MultitapeTM.step,transition,embed,oldTape,innerTape]
    · have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp [MultitapeTM.step,transition,embed,oldTape,innerTape,hi,hv]
  · funext i
    by_cases hi : i = 0
    · subst i
      simp [MultitapeTM.step,transition,embed,oldTape,innerTape]
    · have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp [MultitapeTM.step,transition,embed,oldTape,innerTape,hi,hv]

theorem run_embed (M : MultitapeTM) (rootCells : ℕ → M.Sym) (rootHead : ℕ) (c : M.Cfg) (t : ℕ) :
    (machine M).step^[t] (embed M rootCells rootHead c) = embed M rootCells rootHead (M.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_embed,Function.iterate_succ_apply']

end BitDFT.WorkRelocation
open BitDFT.WorkRelocation IntMul

theorem solution (M : MultitapeTM) (rootCells : ℕ → M.Sym) (rootHead : ℕ) (c : M.Cfg) (t : ℕ) :
    (machine M).step^[t] (embed M rootCells rootHead c) = embed M rootCells rootHead (M.step^[t] c) ∧
      ((machine M).step^[t] (embed M rootCells rootHead c)).cells (machine M).inTape = rootCells ∧
      ((machine M).step^[t] (embed M rootCells rootHead c)).head (machine M).inTape = rootHead := by
  rw [run_embed]
  exact ⟨rfl,rfl,rfl⟩
