-- Prove2me | solution 1 for BitDFT.preprocessor_placement_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:13:56.750372+00:00
-- url     : https://prove2.me/submissions/263cd717-0ff6-4991-9f64-48e413496685

import Definitions.Def_BitDFT_PreprocessorPlacement
import Theorems.Thm_BitDFT_rewrite_input_correct
import Theorems.Thm_BitDFT_vector_encoding_length
import Mathlib.Tactic.Linarith
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Theorems.Thm_BitDFT_alphabet_embedding_correct

noncomputable section
namespace BitDFT.PlacementAlphabetProof
open IntMul BitDFT.AlphabetEmbedding
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

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


end BitDFT.PlacementAlphabetProof
namespace BitDFT.PlacementExtensionProof
open IntMul BitDFT.TapeExtension
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem init_embed (M : MultitapeTM) (r : ℕ) (x y : List Bool) :
    (machine M r).initCfg x y =
      embed M r (fun _ => M.tapeOf []) (fun _ => 0) (M.initCfg x y) := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val < M.k
    · simp [MultitapeTM.initCfg, MultitapeTM.inTape, embed, hi, Fin.ext_iff,
        MultitapeTM.tapeOf, MultitapeTM.bitSym]
      rfl
    · have hz : i.val ≠ 0 := by have := M.two_le_k; omega
      simp [MultitapeTM.initCfg, MultitapeTM.inTape, embed, hi, Fin.ext_iff, hz,
        MultitapeTM.tapeOf]
      rfl
  · funext i; simp [MultitapeTM.initCfg, embed]


end BitDFT.PlacementExtensionProof
namespace BitDFT.PlacementPermutationProof
open IntMul BitDFT.TapePermutation
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl


theorem init_embed (M : MultitapeTM) (e : Fin M.k ≃ Fin M.k) (he : e M.inTape = M.inTape)
    (x y : List Bool) : embed M e he (M.initCfg x y) = (machine M e he).initCfg x y := by
  apply cfg_ext
  · rfl
  · funext i
    have hi : e.symm i = M.inTape ↔ i = M.inTape := by
      constructor
      · intro h
        have hh := congrArg e h
        simpa [he] using hh
      · intro h
        apply e.injective
        simpa [he] using h
    change (if e.symm i = M.inTape then M.tapeOf (x.map M.bitSym++M.sep::y.map M.bitSym) else M.tapeOf []) =
      (if i = M.inTape then M.tapeOf (x.map M.bitSym++M.sep::y.map M.bitSym) else M.tapeOf [])
    simp only [hi]
  · rfl
end BitDFT.PlacementPermutationProof

namespace BitDFT.PreprocessorPlacement
open IntMul

theorem run_embed (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (t : ℕ) :
    (machine N r).step^[t] (embed N r c) = embed N r (RewriteInput.machine.step^[t] c) := by
  unfold embed
  rw [BitDFT.tape_permutation_run]
  rw [(BitDFT.tape_extension_correct (PreprocessorAlphabet.machine N) r).1]
  rw [(BitDFT.alphabet_embedding_correct RewriteInput.machine N (PreprocessorAlphabet.alphabetMap N)).1]

theorem output_cells (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) :
    (embed N r c).cells (machine N r).outTape =
      fun p => PreprocessorAlphabet.encode N (c.cells RewriteInput.machine.outTape p) := by
  rfl

theorem output_head (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) :
    (embed N r c).head (machine N r).outTape = c.head RewriteInput.machine.outTape := by
  rfl

theorem fresh_banks (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg)
    (i : Fin (machine N r).k) (hlo : 2 ≤ i.val) (hhi : i.val < r+2) :
    (embed N r c).cells i = N.tapeOf [] ∧ (embed N r c).head i = 0 := by
  have hv : ((routing N r).symm i).val = i.val+3 := by
    dsimp [routing,CallerRouting.permutation]
    split_ifs <;> omega
  have hf : ¬ ((routing N r).symm i).val < (PreprocessorAlphabet.machine N).k := by
    change ¬ ((routing N r).symm i).val < 5
    omega
  simp [embed,TapePermutation.embed,TapeExtension.embed,hf]


theorem init_embed (N : MultitapeTM) (r : ℕ) (x y : List Bool) :
    embed N r (RewriteInput.machine.initCfg x y) = (machine N r).initCfg x y := by
  unfold embed
  rw [PlacementAlphabetProof.init_embed]
  have hh : TapeExtension.embed (PreprocessorAlphabet.machine N) r
      (fun _ => N.tapeOf []) (fun _ => 0) ((PreprocessorAlphabet.machine N).initCfg x y) =
      (extended N r).initCfg x y := PlacementExtensionProof.init_embed (PreprocessorAlphabet.machine N) r x y |>.symm
  rw [hh]
  exact PlacementPermutationProof.init_embed _ _ _ x y

theorem native_run (N : MultitapeTM) (r : ℕ) (x y : List Bool) (t : ℕ) :
    (machine N r).step^[t] ((machine N r).initCfg x y) =
      embed N r (RewriteInput.machine.step^[t] (RewriteInput.machine.initCfg x y)) := by
  rw [← init_embed,run_embed]


theorem encoded_output (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool)
    (h : c.cells RewriteInput.machine.outTape = RewriteInput.machine.tapeOf (w.map RewriteInput.machine.bitSym)) :
    (embed N r c).cells (machine N r).outTape = (machine N r).tapeOf (w.map (machine N r).bitSym) := by
  rw [output_cells,h]
  have hh := PlacementAlphabetProof.tape_embed (PreprocessorAlphabet.alphabetMap N) (w.map RewriteInput.machine.bitSym)
  have hm : (w.map RewriteInput.machine.bitSym).map (PreprocessorAlphabet.alphabetMap N).encode =
      w.map (machine N r).bitSym := by
    rw [List.map_map]
    congr 1
    funext b
    cases b <;> rfl
  rw [hm] at hh
  exact hh

end BitDFT.PreprocessorPlacement
open BitDFT.PreprocessorPlacement BitDFT IntMul

theorem solution (N : MultitapeTM) (r n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    let q := guardPrecision n b
    let P := machine N r
    ∃ t v, t ≤ 27*n*q ∧
      P.step^[t] (P.initCfg (requestedInput b U) []) = embed N r (RewriteInput.final n b (encVector (q+1) U) v) ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).state = P.qHalt ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).cells P.outTape = P.tapeOf ((fourierInput q U).map P.bitSym) ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).head P.outTape = (fourierInput q U).length+1 ∧
      (∀ i : Fin P.k, 2 ≤ i.val → i.val < r+2 →
        (P.step^[t] (P.initCfg (requestedInput b U) [])).cells i = N.tapeOf [] ∧
        (P.step^[t] (P.initCfg (requestedInput b U) [])).head i = 0) := by
  dsimp only
  let q := guardPrecision n b
  obtain ⟨t,v,ht,hv,hlen,hr⟩ := BitDFT.rewrite_input_correct n b hn hb (encVector (q+1) U)
  have hq : 1 ≤ q := by unfold q guardPrecision; omega
  have hlenr : (encVector (q+1) U).length = 2*n*(q+2) := by
    simpa [Nat.add_assoc] using BitDFT.vector_encoding_length (q+1) U
  rw [hlenr] at ht
  have ht' : t ≤ 27*n*q := by
    have hqn : q ≤ n*q := by nlinarith
    have hnq : n ≤ n*q := by nlinarith
    have hnqpos : 1 ≤ n*q := by nlinarith
    change t ≤ 19*q+2*n*(q+2)+2 at ht
    nlinarith
  have he : (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
      embed N r (RewriteInput.final n b (encVector (q+1) U) v) := by
    rw [native_run]
    exact congrArg (embed N r) hr
  refine ⟨t,v,ht',he,?_,?_,?_,?_⟩
  · rw [he]; rfl
  · rw [he]
    apply encoded_output
    rfl
  · rw [he,output_head]
    rfl
  · intro i hlo hhi
    rw [he]
    exact fresh_banks N r _ i hlo hhi

