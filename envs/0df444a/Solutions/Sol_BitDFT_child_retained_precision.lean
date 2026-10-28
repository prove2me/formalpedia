-- Prove2me | solution 1 for BitDFT.child_retained_precision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:07:45.331443+00:00
-- url     : https://prove2.me/submissions/2859e864-2f7c-4cfa-acb0-732378f78d61

import Definitions.Def_BitDFT_NativeChildOutput
import Mathlib.Tactic
open BitDFT IntMul

/-- All three preprocessor workspace tapes survive the arbitrary child and output return. -/
private theorem child_workspace (M : MultitapeTM) (c : RewriteInput.machine.Cfg)
    (x w : List Bool) (T : ℕ) (i : Fin (NativeChildOutput.program M).k)
    (hi : M.k+2 ≤ i.val) :
    let result := NativeChildOutput.final M
      (ChildCall.final M (CallerReady.final (ChildCall.child M) M.k c x) x T w) w
    result.cells i = (PreprocessorPlacement.embed (ChildCall.child M) M.k c).cells i ∧
    result.head i = (PreprocessorPlacement.embed (ChildCall.child M) M.k c).head i := by
  have hc : ¬i.val < (ChildCall.child M).k := by change ¬i.val < M.k+2; omega
  have ho : ¬i.val < (NativeChildOutput.child M).k := by change ¬i.val < M.k+2; omega
  have htwo : ¬i.val < 2 := by omega
  have hone : ¬ i.val ≤ 1 := by omega
  simp [NativeChildOutput.final,NativeChildOutput.embed,ChildCall.final,ChildCall.embed,
    CallerReady.final,BankHeadSetup.finish,BankHeadSetup.selected,
    PrepareCall.final,PrepareCall.shiftFinish,BufferShiftOn.embed,PrepareCall.shiftBase,
    MachineSequence.rightCfg,MachineSequence.handoff,hc,ho,htwo,hone,show ¬ i.val < M.k+2 by omega]

open BitDFT IntMul

/-- Identify a routed original workspace tape after alphabet lifting and extension. -/
private theorem placed_workspace (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg)
    (j : Fin 5) (hj : 2 ≤ j.val) :
    let i : Fin (PreprocessorPlacement.machine N r).k := ⟨j.val+r,by have := j.isLt; change j.val+r < 5+r; omega⟩
    (PreprocessorPlacement.embed N r c).cells i =
      (fun p => PreprocessorAlphabet.encode N (c.cells j p)) ∧
    (PreprocessorPlacement.embed N r c).head i = c.head j := by
  have hlarge : ¬j.val+r < 2 := by omega
  have hbank : ¬j.val+r < r+2 := by omega
  have hone : ¬j.val+r ≤ 1 := by omega
  have hsub : j.val+r-r = j.val := by omega
  simp [PreprocessorPlacement.embed,TapePermutation.embed,TapeExtension.embed,
    AlphabetEmbedding.embed,PreprocessorPlacement.routing,CallerRouting.permutation,
    hlarge,hone,hbank,hsub,j.isLt,PreprocessorAlphabet.alphabetMap]
  rfl


private theorem saved_workspace (M : MultitapeTM) (c : RewriteInput.machine.Cfg)
    (x w : List Bool) (T : ℕ) (j : Fin 5) (hj : 2 ≤ j.val) :
    let i : Fin (NativeChildOutput.program M).k := ⟨j.val+M.k,by have := j.isLt; change j.val+M.k < 5+M.k; omega⟩
    let result := NativeChildOutput.final M
      (ChildCall.final M (CallerReady.final (ChildCall.child M) M.k c x) x T w) w
    result.cells i = (fun p => PreprocessorAlphabet.encode (ChildCall.child M) (c.cells j p)) ∧
    result.head i = c.head j := by
  dsimp only
  let i : Fin (NativeChildOutput.program M).k := ⟨j.val+M.k,by have := j.isLt; change j.val+M.k < 5+M.k; omega⟩
  have hpres := child_workspace M c x w T i (by dsimp [i]; omega)
  have hplace := placed_workspace (ChildCall.child M) M.k c j hj
  exact ⟨hpres.1.trans hplace.1,hpres.2.trans hplace.2⟩

/-- The input rewriter leaves canonical precision and dimension on its work tapes. -/
private theorem retained_precision (n b : ℕ) (rest v : List Bool)
    (hv : BinaryCounter.value v = guardPrecision n b) :
    (RewriteInput.final n b rest v).cells 3 = RewriteInput.machine.tapeOf
      ((bin (guardPrecision n b).size (guardPrecision n b)).map RewriteInput.machine.bitSym) ∧
    (RewriteInput.final n b rest v).head 3 = (guardPrecision n b).size+1 ∧
    (RewriteInput.final n b rest v).cells 4 = RewriteInput.machine.tapeOf
      ((true :: (bin n.size n).tail).map RewriteInput.machine.bitSym) ∧
    (RewriteInput.final n b rest v).head 4 = (true :: (bin n.size n).tail).length+1 := by
  simp [RewriteInput.final,RewriteInput.copyBase,SuffixCopy.frame,RewriteHeaders.final,
    HeaderSerialization.final,HeaderSerialization.precisionFinished,
    HeaderSerialization.serializerBase,HeaderSerialization.trimmed,
    HeaderSerialization.trimBase,HeaderSerialization.firstFinished,
    HeaderSerialization.inputBase,SerializeField.frame,TrimReverse.frame,
    TapePermutation.embed,HeaderSerialization.swap34,MachineSequence.rightCfg,hv,
    bin]
  exact ⟨rfl,rfl⟩

private theorem binary_tape_embed (N : MultitapeTM) (w : List Bool) :
    (fun p => PreprocessorAlphabet.encode N
      (RewriteInput.machine.tapeOf (w.map RewriteInput.machine.bitSym) p)) =
      N.tapeOf (w.map N.bitSym) := by
  funext p
  cases p with
  | zero => rfl
  | succ p =>
    simp only [MultitapeTM.tapeOf,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases h : w[p]? with
    | none => simp [h,PreprocessorAlphabet.encode]
    | some b => cases b <;> simp [h,MultitapeTM.bitSym,PreprocessorAlphabet.encode]

theorem solution (M : MultitapeTM) (n b : ℕ) (rest v x w : List Bool) (T : ℕ)
    (hv : BinaryCounter.value v = guardPrecision n b) :
    let i : Fin (NativeChildOutput.program M).k := ⟨3+M.k,by change 3+M.k < 5+M.k; omega⟩
    let result := NativeChildOutput.final M
      (ChildCall.final M (CallerReady.final (ChildCall.child M) M.k
        (RewriteInput.final n b rest v) x) x T w) w
    result.cells i = (NativeChildOutput.program M).tapeOf
      ((bin (guardPrecision n b).size (guardPrecision n b)).map (NativeChildOutput.program M).bitSym) ∧
    result.head i = (guardPrecision n b).size+1 := by
  have hs := saved_workspace M (RewriteInput.final n b rest v) x w T 3 (by decide)
  have hr := retained_precision n b rest v hv
  constructor
  · change _ = (ChildCall.child M).tapeOf _
    refine hs.1.trans ?_
    rw [hr.1]
    exact binary_tape_embed (ChildCall.child M) _
  · exact hs.2.trans hr.2.1
