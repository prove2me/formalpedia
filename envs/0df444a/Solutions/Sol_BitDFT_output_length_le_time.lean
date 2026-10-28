-- Prove2me | solution 1 for BitDFT.output_length_le_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:38:52.081225+00:00
-- url     : https://prove2.me/submissions/ba6f9b70-2ef5-4d61-be92-72f46f2f0ebe

import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum
set_option autoImplicit false
open IntMul

private lemma head_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    ∀ i, (M.step^[t] (M.initCfg x y)).head i ≤ t := by
  induction t with
  | zero => simp [MultitapeTM.initCfg]
  | succ t ih =>
    intro i
    rw [Function.iterate_succ_apply']
    simp only [MultitapeTM.step]
    split <;> have hi := ih i <;> omega

private lemma unvisited_output_blank (M : MultitapeTM) (x y : List Bool) (t p : ℕ) (hp : t < p) :
    (M.step^[t] (M.initCfg x y)).cells M.outTape p = M.blank := by
  induction t with
  | zero =>
    have hoi : M.outTape ≠ M.inTape := by
      simp [MultitapeTM.outTape, MultitapeTM.inTape]
    cases p with
    | zero => omega
    | succ p => simp [MultitapeTM.initCfg, hoi, MultitapeTM.tapeOf]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hhead := head_bound M x y t M.outTape
    have hne : p ≠ (M.step^[t] (M.initCfg x y)).head M.outTape := by omega
    simp only [MultitapeTM.step, Function.update_of_ne hne]
    exact ih (by omega)

theorem solution (M : MultitapeTM) (x y w : List Bool) (t : ℕ)
    (h : M.HaltsWithOutput x y t w) : w.length ≤ t := by
  by_contra hlt
  have hp : t < w.length := by omega
  have hp0 : 0 < w.length := by omega
  have hb := unvisited_output_blank M x y t w.length hp
  rw [h.2] at hb
  have he : w.length = (w.length - 1) + 1 := by omega
  rw [he, MultitapeTM.tapeOf] at hb
  have hi : w.length - 1 < w.length := by omega
  have him : w.length - 1 < (w.map M.bitSym).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ him] at hb
  simp only [List.getElem_map] at hb
  have hd := M.syms_distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  have hz : M.blank ≠ M.zero := hd.1.2.1
  have ho : M.blank ≠ M.one := hd.1.2.2.1
  have hb' : M.bitSym (w[w.length - 1]) = M.blank := hb
  cases hw : w[w.length - 1] with
  | false =>
    have hzero : M.zero = M.blank := by simpa only [hw, MultitapeTM.bitSym, Bool.false_eq_true, if_false] using hb'
    exact hz hzero.symm
  | true =>
    have hone : M.one = M.blank := by simpa only [hw, MultitapeTM.bitSym, if_true] using hb'
    exact ho hone.symm

