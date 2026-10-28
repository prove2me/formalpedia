-- Prove2me | solution 1 for BitDFT.alphabet_embedding_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:48:17.256188+00:00
-- url     : https://prove2.me/submissions/4a1820c7-02c6-41f6-a66c-93b7f3d15cad

import Definitions.Def_BitDFT_AlphabetEmbedding

namespace BitDFT.AlphabetEmbedding
open IntMul

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem transition_encoded {M N : MultitapeTM} (e : Map M N) (q : M.K) (a : Fin M.k → M.Sym) :
    transition e q (fun i => e.encode (a i)) =
      ((M.δ q a).1,fun i => (e.encode ((M.δ q a).2 i).1,((M.δ q a).2 i).2)) := by
  classical
  unfold transition
  by_cases h : q = M.qHalt
  · subst q
    simp [M.halt_fixed]
  · simp only [h,if_false,decode_encode]
    congr 1
    funext i
    by_cases hi : i = M.inTape
    · subst i
      simp only [if_true]
      change (e.encode (a M.inTape),((M.δ q a).2 M.inTape).2) = _
      apply Prod.ext
      · exact congrArg e.encode (M.input_readonly q a).symm
      · rfl
    · simp only [hi,if_false]

theorem step_embed {M N : MultitapeTM} (e : Map M N) (c : M.Cfg) :
    (machine e).step (embed e c) = embed e (M.step c) := by
  apply cfg_ext
  · simp [MultitapeTM.step,embed,transition_encoded]
  · funext i p
    change Function.update (fun j => e.encode (c.cells i j)) (c.head i)
      ((transition e c.state (fun j => e.encode (c.cells j (c.head j)))).2 i).1 p = _
    rw [transition_encoded]
    by_cases hp : p = c.head i
    · subst p
      simp [embed,MultitapeTM.step]
    · simp [Function.update_of_ne hp,embed,MultitapeTM.step,hp]
  · simp [MultitapeTM.step,embed,transition_encoded]

theorem run_embed {M N : MultitapeTM} (e : Map M N) (c : M.Cfg) (t : ℕ) :
    (machine e).step^[t] (embed e c) = embed e (M.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_embed,Function.iterate_succ_apply']

theorem tape_embed {M N : MultitapeTM} (e : Map M N) (w : List M.Sym) :
    (fun p => e.encode (M.tapeOf w p)) = (machine e).tapeOf (w.map e.encode) := by
  funext p
  cases p with
  | zero => exact e.marker
  | succ p =>
    simp [MultitapeTM.tapeOf]
    cases h : w[p]? <;> simp [h,e.blank]

theorem bits_embed {M N : MultitapeTM} (e : Map M N) (b : Bool) :
    e.encode (M.bitSym b) = (machine e).bitSym b := by
  cases b <;> simp [MultitapeTM.bitSym,e.zero,e.one]

theorem init_embed {M N : MultitapeTM} (e : Map M N) (x y : List Bool) :
    embed e (M.initCfg x y) = (machine e).initCfg x y := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i = M.inTape
    · simp [embed,MultitapeTM.initCfg,hi,tape_embed,List.map_append,List.map_map,
        Function.comp_def,e.sep,bits_embed,MultitapeTM.inTape]
    · have hi' : i ≠ (machine e).inTape := hi
      simp only [embed,MultitapeTM.initCfg,hi,hi',if_false]
      simpa using tape_embed e []
  · rfl

theorem halts_embed {M N : MultitapeTM} (e : Map M N) (x y : List Bool) (t : ℕ) (w : List Bool)
    (h : M.HaltsWithOutput x y t w) : (machine e).HaltsWithOutput x y t w := by
  rcases h with ⟨hs,ho⟩
  unfold MultitapeTM.HaltsWithOutput
  rw [← init_embed e x y,run_embed]
  constructor
  · exact hs
  · change (fun p => e.encode ((M.step^[t] (M.initCfg x y)).cells M.outTape p)) = _
    rw [ho,tape_embed]
    simp [List.map_map,Function.comp_def,bits_embed]

end BitDFT.AlphabetEmbedding
open BitDFT.AlphabetEmbedding IntMul

theorem solution (M N : MultitapeTM) (e : Map M N) :
    (∀ (c : M.Cfg) (t : ℕ), (machine e).step^[t] (embed e c) = embed e (M.step^[t] c)) ∧
    (∀ (x y : List Bool) (t : ℕ) (w : List Bool), M.HaltsWithOutput x y t w →
      (machine e).HaltsWithOutput x y t w) := by
  exact ⟨fun c t => run_embed e c t,fun x y t w h => halts_embed e x y t w h⟩

