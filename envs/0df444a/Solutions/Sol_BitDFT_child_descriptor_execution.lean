-- Prove2me | solution 1 for BitDFT.child_descriptor_execution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:47:54.858312+00:00
-- url     : https://prove2.me/submissions/7001f9c6-f59c-46a6-96f5-a3686e869fa0

import Theorems.Thm_BitDFT_native_child_output_with_precision
import Theorems.Thm_BitDFT_child_retained_precision
import Theorems.Thm_BitDFT_descriptor_placement_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic
import Theorems.Thm_BitDFT_descriptor_initial_match
import Definitions.Def_BitDFT_ChildDescriptor
import Theorems.Thm_BitDFT_tape_count_transport_correct
import Theorems.Thm_BitDFT_tape_extension_correct
namespace BitDFT.ChildDescriptor
open IntMul

theorem prepared_run (M : MultitapeTM) (c : (NativeChildOutput.program M).Cfg) (t : ℕ) :
    (preparation M).step^[t] (prepared M c) =
      prepared M ((NativeChildOutput.program M).step^[t] c) := by
  unfold prepared
  rw [BitDFT.tape_count_transport_correct,
    (BitDFT.tape_extension_correct (NativeChildOutput.program M) 2).1]

theorem fresh_tapes (M : MultitapeTM) (c : (NativeChildOutput.program M).Cfg)
    (i : Fin (4+(M.k+3))) (hi : M.k+5 ≤ i.val) :
    (prepared M c).cells i = (NativeChildOutput.program M).tapeOf [] ∧
    (prepared M c).head i = 0 := by
  have hn : ¬i.val < (NativeChildOutput.program M).k := by change ¬i.val < 5+M.k; omega
  simp [prepared,TapeCountTransport.embed,TapeExtension.embed,hn]



private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem extension_init (M : MultitapeTM) (r : ℕ) (x y : List Bool) :
    (TapeExtension.machine M r).initCfg x y =
      TapeExtension.embed M r (fun _ => M.tapeOf []) (fun _ => 0) (M.initCfg x y) := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val < M.k
    · simp [MultitapeTM.initCfg,MultitapeTM.inTape,TapeExtension.embed,hi,Fin.ext_iff]
      rfl
    · have hz : i.val ≠ 0 := by have := M.two_le_k; omega
      simp [MultitapeTM.initCfg,MultitapeTM.inTape,TapeExtension.embed,hi,Fin.ext_iff,hz]
      rfl
  · funext i; simp [MultitapeTM.initCfg,TapeExtension.embed]

private theorem transport_init (M : MultitapeTM) (n : ℕ) (h : M.k = n) (x y : List Bool) :
    (TapeCountTransport.machine M n h).initCfg x y =
      TapeCountTransport.embed M n h (M.initCfg x y) := by
  subst n
  rfl

theorem prepared_init (M : MultitapeTM) (x y : List Bool) :
    (preparation M).initCfg x y = prepared M ((NativeChildOutput.program M).initCfg x y) := by
  unfold prepared
  rw [← extension_init,← transport_init]

theorem old_tape (M : MultitapeTM) (c : (NativeChildOutput.program M).Cfg)
    (j : Fin (NativeChildOutput.program M).k) :
    let i : Fin (4+(M.k+3)) := ⟨j.val,by have hj : j.val < 5+M.k := j.isLt; omega⟩
    (prepared M c).cells i = c.cells j ∧ (prepared M c).head i = c.head j := by
  simp [prepared,TapeCountTransport.embed,TapeExtension.embed,j.isLt]



private theorem input_embed (N : MultitapeTM) (input : List Bool) :
    (fun p => PreprocessorAlphabet.encode N ((DescriptorSetup.machine.initCfg input []).cells 0 p)) =
      (N.initCfg input []).cells N.inTape := by
  have hb : PreprocessorAlphabet.encode N ∘ DescriptorSetup.machine.bitSym = N.bitSym := by
    funext b; cases b <;> rfl
  change (fun p => PreprocessorAlphabet.encode N
    (DescriptorSetup.machine.tapeOf (input.map DescriptorSetup.machine.bitSym ++ [TapeCopy.Sym.sep]) p)) =
      N.tapeOf (input.map N.bitSym ++ [N.sep])
  funext p
  cases p with
  | zero => rfl
  | succ p =>
    simp only [MultitapeTM.tapeOf,List.getD_eq_getElem?_getD]
    have hm : (input.map DescriptorSetup.machine.bitSym ++ [TapeCopy.Sym.sep]).map (PreprocessorAlphabet.encode N) =
        input.map N.bitSym ++ [N.sep] := by simp [List.map_append,List.map_map,hb,PreprocessorAlphabet.encode]
    rw [← hm,List.getElem?_map]
    cases h : (input.map DescriptorSetup.machine.bitSym ++ [TapeCopy.Sym.sep])[p]? <;>
      simp [h,PreprocessorAlphabet.encode]

theorem setup_match (M : MultitapeTM) (input y : List Bool) (c : (NativeChildOutput.program M).Cfg)
    (hinput : c.cells (NativeChildOutput.program M).inTape =
      ((NativeChildOutput.program M).initCfg input []).cells (NativeChildOutput.program M).inTape)
    (hp : c.cells ⟨M.k+3,by change M.k+3 < 5+M.k; omega⟩ =
      (NativeChildOutput.program M).tapeOf (y.map (NativeChildOutput.program M).bitSym))
    (hpHead : c.head ⟨M.k+3,by change M.k+3 < 5+M.k; omega⟩ = y.length+1) :
    DescriptorPlacement.embed (NativeChildOutput.program M) M.k (setupStart M c).cells (setupStart M c).head
      (RewoundDescriptor.initial (sourceBase input (c.head (NativeChildOutput.program M).inTape)) y) =
      setupStart M c := by
  let d := setupStart M c
  let base := sourceBase input (c.head (NativeChildOutput.program M).inTape)
  have h0 := old_tape M c (NativeChildOutput.program M).inTape
  have h3 := old_tape M c ⟨M.k+3,by change M.k+3 < 5+M.k; omega⟩
  have hcounter := fresh_tapes M c (DescriptorPlacement.counterTape M.k) (by simp [DescriptorPlacement.counterTape])
  have htemplate := fresh_tapes M c (DescriptorPlacement.templateTape M.k) (by simp [DescriptorPlacement.templateTape])
  apply BitDFT.descriptor_initial_match (NativeChildOutput.program M) M.k M.two_le_k d base y
  · rfl
  · change (prepared M c).cells ⟨0,by change 0 < 4+(M.k+3); omega⟩ = _
    refine h0.1.trans (hinput.trans ?_)
    exact (input_embed (NativeChildOutput.program M) input).symm
  · exact h0.2
  · exact h3.1.trans hp
  · exact h3.2.trans hpHead
  · exact hcounter.1
  · exact hcounter.2
  · exact htemplate.1
  · exact htemplate.2

end BitDFT.ChildDescriptor

namespace BitDFT.NativeInputPreservation
open IntMul

theorem step_cells (M : MultitapeTM) (c : M.Cfg) :
    (M.step c).cells M.inTape = c.cells M.inTape := by
  change Function.update (c.cells M.inTape) (c.head M.inTape)
    ((M.δ c.state (fun i => c.cells i (c.head i))).2 M.inTape).1 = _
  have hr : ((M.δ c.state (fun i => c.cells i (c.head i))).2 M.inTape).1 =
      c.cells M.inTape (c.head M.inTape) := M.input_readonly _ _
  rw [hr]
  exact Function.update_eq_self _ _

theorem run_cells (M : MultitapeTM) (c : M.Cfg) (t : ℕ) :
    (M.step^[t] c).cells M.inTape = c.cells M.inTape := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',step_cells,ih]

end BitDFT.NativeInputPreservation
open BitDFT.ChildDescriptor BitDFT IntMul MachineSequence

theorem solution (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 190*n*q+10*T ∧ BinaryCounter.value v = q ∧
      (machine M).step^[t] ((machine M).initCfg (requestedInput b U) []) =
        final M (requestedInput b U)
          (NativeChildOutput.final M (ChildCall.final M
            (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w)
          (bin q.size q) := by
  dsimp only
  let q := guardPrecision n b
  let input := requestedInput b U
  let x := fourierInput q U
  let y := bin q.size q
  obtain ⟨s,v,hs,hv,hr,_,_⟩ := BitDFT.native_child_output_with_precision M n b hn hb U T halt w out
  let c := NativeChildOutput.final M (ChildCall.final M
    (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w
  have hrun : (NativeChildOutput.program M).step^[s] ((NativeChildOutput.program M).initCfg input []) = c := hr
  have hinput : c.cells (NativeChildOutput.program M).inTape =
      ((NativeChildOutput.program M).initCfg input []).cells (NativeChildOutput.program M).inTape := by
    rw [← hrun]
    exact NativeInputPreservation.run_cells _ _ _
  have hp := BitDFT.child_retained_precision M n b (encVector (q+1) U) v x w T hv
  have hp' : c.cells ⟨M.k+3,by change M.k+3 < 5+M.k; omega⟩ =
      (NativeChildOutput.program M).tapeOf (y.map (NativeChildOutput.program M).bitSym) ∧
      c.head ⟨M.k+3,by change M.k+3 < 5+M.k; omega⟩ = y.length+1 := by
    simpa [c,y,q,bin,Nat.add_comm] using hp
  have hmatch := setup_match M input y c hinput hp'.1 hp'.2
  obtain ⟨u,hu,hsetup,_⟩ := BitDFT.descriptor_placement_correct (NativeChildOutput.program M) M.k
    (setupStart M c).cells (setupStart M c).head
    (sourceBase input (c.head (NativeChildOutput.program M).inTape)) y
  rw [hmatch] at hsetup
  have hprep : (preparation M).step^[s] ((preparation M).initCfg input []) = prepared M c := by
    rw [prepared_init,prepared_run,hrun]
  have hhalt : ((preparation M).step^[s] ((preparation M).initCfg input [])).state =
      (native (preparation M)).exit := by
    rw [hprep]
    rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (native (preparation M)) (setupControl M)
    ((preparation M).initCfg input []) s u hhalt
  change (machine M).step^[t] ((machine M).initCfg input []) =
    rightCfg (native (preparation M)) (setupControl M)
      ((setupControl M).machine.step^[u] (handoff (native (preparation M)) (setupControl M)
        ((preparation M).step^[s] ((preparation M).initCfg input [])))) at he
  rw [hprep] at he
  change (machine M).step^[t] ((machine M).initCfg input []) =
    rightCfg (native (preparation M)) (setupControl M)
      ((setup M).step^[u] (setupStart M c)) at he
  rw [hsetup] at he
  refine ⟨t,v,?_,hv,he⟩
  have hq : 1 ≤ q := by dsimp [q,guardPrecision]; omega
  have hsize : q.size ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
  have hyl : y.length = q.size := by simp [y,bin]
  rw [hyl] at hu
  change s ≤ 181*n*q+10*T at hs
  have hnq : q ≤ n*q := by nlinarith
  nlinarith
