-- Prove2me | solution 1 for BitDFT.first_coordinate_request
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:02:32.160168+00:00
-- url     : https://prove2.me/submissions/9c1fc222-6c1a-4d5f-b016-f5ab08f2abb2

import Definitions.Def_BitDFT_VectorReady
import Theorems.Thm_BitDFT_descriptor_slots
import Theorems.Thm_BitDFT_vector_ready
import Theorems.Thm_BitDFT_extraction_ready
import Theorems.Thm_BitDFT_signed_block_placement_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Definitions.Def_BitDFT_FirstCoordinate
import Theorems.Thm_BitDFT_signed_block_initial_match
import Definitions.Def_IntMul_MultitapeModel

namespace BitDFT.VectorReadyDescriptors
open IntMul DescriptorPlacement

private theorem counter_ne_output (M : MultitapeTM) : counterTape M.k ≠ (VectorReady.preparation M).outTape := by
  intro h
  have he := congrArg Fin.val h
  have hm : 1 % (4+(M.k+3)) = 1 := Nat.mod_eq_of_lt (by omega)
  change M.k+5 = 1 % (4+(M.k+3)) at he
  rw [hm] at he
  omega
private theorem template_ne_output (M : MultitapeTM) : templateTape M.k ≠ (VectorReady.preparation M).outTape := by
  intro h
  have he := congrArg Fin.val h
  have hm : 1 % (4+(M.k+3)) = 1 := Nat.mod_eq_of_lt (by omega)
  change M.k+6 = 1 % (4+(M.k+3)) at he
  rw [hm] at he
  omega
end BitDFT.VectorReadyDescriptors
open BitDFT.VectorReadyDescriptors BitDFT IntMul

private theorem descriptors (M : MultitapeTM) (input y : List Bool) (c : (NativeChildOutput.program M).Cfg) :
    let d := VectorReady.final M input c y
    let N := VectorReady.machine M
    d.cells (DescriptorPlacement.counterTape M.k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    d.head (DescriptorPlacement.counterTape M.k) = y.length+1 ∧
    d.cells (DescriptorPlacement.templateTape M.k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    d.head (DescriptorPlacement.templateTape M.k) = y.length+1 := by
  obtain ⟨_,_,_,_,_,_,_,_,hc,hch,ht,hth⟩ := BitDFT.descriptor_slots
    (NativeChildOutput.program M) M.k M.two_le_k
    (ChildDescriptor.setupStart M c).cells (ChildDescriptor.setupStart M c).head
    (ChildDescriptor.sourceBase input (c.head (NativeChildOutput.program M).inTape)) y
  refine ⟨hc,?_,ht,?_⟩
  · change Function.update (ChildDescriptor.final M input c y).head (VectorReady.preparation M).outTape 1
      (DescriptorPlacement.counterTape M.k) = _
    rw [Function.update_of_ne (counter_ne_output M)]
    exact hch
  · change Function.update (ChildDescriptor.final M input c y).head (VectorReady.preparation M).outTape 1
      (DescriptorPlacement.templateTape M.k) = _
    rw [Function.update_of_ne (template_ne_output M)]
    exact hth


namespace BitDFT.FirstCoordinate
open IntMul MachineSequence

theorem old_slot (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (j : Fin (VectorReady.machine M).k) :
    let i : Fin (5+(M.k+3)) := ⟨j.val,by have hj : j.val < 4+(M.k+3) := j.isLt; omega⟩
    (start M c).cells i = c.cells j ∧ (start M c).head i = c.head j := by
  have hj : j.val < 4+(M.k+3) := j.isLt
  have hn : j.val ≠ M.k+7 := by omega
  simp [start,handoff,ExtractionReady.final,rightCfg,RewindTape.frame,
    ExtractionReady.prepared,TapeCountTransport.embed,TapeExtension.embed,j.isLt,
    ExtractionReady.scratch,SignedBlockPlacement.scratchTape,Fin.ext_iff,hn]

theorem fresh_slot (M : MultitapeTM) (c : (VectorReady.machine M).Cfg) :
    (start M c).cells (SignedBlockPlacement.scratchTape M.k) = (VectorReady.machine M).tapeOf [] ∧
    (start M c).head (SignedBlockPlacement.scratchTape M.k) = 1 := by
  have hn : ¬ M.k+7 < (VectorReady.machine M).k := by change ¬ M.k+7 < 4+(M.k+3); omega
  simp [start,handoff,ExtractionReady.final,rightCfg,RewindTape.frame,
    ExtractionReady.prepared,TapeCountTransport.embed,TapeExtension.embed,
    ExtractionReady.scratch,SignedBlockPlacement.scratchTape,hn]

end BitDFT.FirstCoordinate
open BitDFT.FirstCoordinate BitDFT IntMul

private theorem setup_match (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ) (sign : Bool) (x y : List Bool)
    (hroot : c.cells ⟨0,by change 0 < 4+(M.k+3); omega⟩ = fun p => PreprocessorAlphabet.encode (VectorReady.machine M) (rootCells p))
    (hrootHead : c.head ⟨0,by change 0 < 4+(M.k+3); omega⟩ = rootHead)
    (hv : c.cells ⟨1,by change 1 < 4+(M.k+3); omega⟩ = (VectorReady.machine M).tapeOf ((sign::x).map (VectorReady.machine M).bitSym))
    (hvHead : c.head ⟨1,by change 1 < 4+(M.k+3); omega⟩ = 1)
    (hc : c.cells (DescriptorPlacement.counterTape M.k) = (VectorReady.machine M).tapeOf ((VectorReady.machine M).sep :: (y.map (VectorReady.machine M).bitSym ++ [(VectorReady.machine M).sep])))
    (hcHead : c.head (DescriptorPlacement.counterTape M.k) = y.length+1)
    (ht : c.cells (DescriptorPlacement.templateTape M.k) = (VectorReady.machine M).tapeOf ((VectorReady.machine M).sep :: (y.map (VectorReady.machine M).bitSym ++ [(VectorReady.machine M).sep])))
    (htHead : c.head (DescriptorPlacement.templateTape M.k) = y.length+1) :
    SignedBlockPlacement.embed (VectorReady.machine M) M.k (start M c).cells (start M c).head
      (WorkRelocation.embed SignedBlock.machine rootCells rootHead (SignedBlock.initial [] [] sign x y)) = start M c := by
  have h0 := old_slot M c ⟨0,by change 0 < 4+(M.k+3); omega⟩
  have h1 := old_slot M c ⟨1,by change 1 < 4+(M.k+3); omega⟩
  have h2 := old_slot M c (DescriptorPlacement.counterTape M.k)
  have h3 := old_slot M c (DescriptorPlacement.templateTape M.k)
  have h4 := fresh_slot M c
  apply BitDFT.signed_block_initial_match (VectorReady.machine M) M.k (start M c)
    rootCells rootHead [] [] sign x y rfl
  · exact h0.1.trans hroot
  · exact h0.2.trans hrootHead
  · exact h1.1.trans hv
  · exact h1.2.trans hvHead
  · exact h4.1
  · exact h4.2
  · exact h2.1.trans hc
  · exact h2.2.trans hcHead
  · exact h3.1.trans ht
  · exact h3.2.trans htHead

open MachineSequence
private theorem extract_run (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (input extra : List Bool) (T : ℕ)
    (hrun : (VectorReady.machine M).step^[T] ((VectorReady.machine M).initCfg input extra) = c)
    (hhalt : c.state = (VectorReady.machine M).qHalt)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ) (sign : Bool) (x y : List Bool)
    (hroot : c.cells ⟨0,by change 0 < 4+(M.k+3); omega⟩ = fun p => PreprocessorAlphabet.encode (VectorReady.machine M) (rootCells p))
    (hrootHead : c.head ⟨0,by change 0 < 4+(M.k+3); omega⟩ = rootHead)
    (hv : c.cells ⟨1,by change 1 < 4+(M.k+3); omega⟩ = (VectorReady.machine M).tapeOf ((sign::x).map (VectorReady.machine M).bitSym))
    (hvHead : c.head ⟨1,by change 1 < 4+(M.k+3); omega⟩ = 1)
    (hc : c.cells (DescriptorPlacement.counterTape M.k) = (VectorReady.machine M).tapeOf ((VectorReady.machine M).sep :: (y.map (VectorReady.machine M).bitSym ++ [(VectorReady.machine M).sep])))
    (hcHead : c.head (DescriptorPlacement.counterTape M.k) = y.length+1)
    (ht : c.cells (DescriptorPlacement.templateTape M.k) = (VectorReady.machine M).tapeOf ((VectorReady.machine M).sep :: (y.map (VectorReady.machine M).bitSym ++ [(VectorReady.machine M).sep])))
    (htHead : c.head (DescriptorPlacement.templateTape M.k) = y.length+1)
    (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ T+6*(val y+1)+4*y.length+7 ∧
      (machine M).step^[t] ((machine M).initCfg input extra) = final M c rootCells rootHead sign x y := by
  have halt : ((VectorReady.machine M).step^[T] ((VectorReady.machine M).initCfg input extra)).state =
      (VectorReady.machine M).qHalt := by rw [hrun]; exact hhalt
  obtain ⟨s,hs,hprep⟩ := BitDFT.extraction_ready M input extra T halt
  rw [hrun] at hprep
  have hm := setup_match M c rootCells rootHead sign x y hroot hrootHead hv hvHead hc hcHead ht htHead
  obtain ⟨u,hu,hextract,_⟩ := BitDFT.signed_block_placement_correct (VectorReady.machine M) M.k
    (start M c).cells (start M c).head rootCells rootHead [] [] sign x y hx
  rw [hm] at hextract
  have hh : ((storage M).step^[s] ((storage M).initCfg input extra)).state =
      (native (storage M)).exit := by rw [hprep]; rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (native (storage M)) (control M)
    ((storage M).initCfg input extra) s u hh
  change (machine M).step^[t] ((machine M).initCfg input extra) =
    rightCfg (native (storage M)) (control M)
      ((control M).machine.step^[u] (handoff (native (storage M)) (control M)
        ((storage M).step^[s] ((storage M).initCfg input extra)))) at he
  rw [hprep] at he
  change (machine M).step^[t] ((machine M).initCfg input extra) =
    rightCfg (native (storage M)) (control M) ((extractor M).step^[u] (start M c)) at he
  rw [hextract] at he
  exact ⟨t,by omega,he⟩

namespace BitDFT.FirstCoordinateInput
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

end BitDFT.FirstCoordinateInput

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


open BitDFT.FirstCoordinate BitDFT IntMul MachineSequence

theorem solution (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (sign : Bool) (x : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf ((sign::x).map M.bitSym))
    (hx : val (bin (guardPrecision n b).size (guardPrecision n b))+1 ≤ x.length) :
    let q := guardPrecision n b
    let y := bin q.size q
    ∃ t v,
      let c := VectorReady.final M (requestedInput b U)
        (NativeChildOutput.final M (ChildCall.final M
          (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v)
            (fourierInput q U)) (fourierInput q U) T (sign::x)) (sign::x)) y
      t ≤ 193*n*q+11*T+6*(val y+1)+4*y.length+7 ∧ BinaryCounter.value v = q ∧
      (machine M).step^[t] ((machine M).initCfg (requestedInput b U) []) =
        final M c ((DescriptorSetup.machine.initCfg (requestedInput b U) []).cells 0)
          (c.head (VectorReady.machine M).inTape) sign x y := by
  dsimp only
  let q := guardPrecision n b
  let y := bin q.size q
  let input := requestedInput b U
  obtain ⟨s,v,hs,hv,hr,hout,hhead⟩ := BitDFT.vector_ready M n b hn hb U T halt (sign::x) out
  let child := NativeChildOutput.final M (ChildCall.final M
    (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v)
      (fourierInput q U)) (fourierInput q U) T (sign::x)) (sign::x)
  let c := VectorReady.final M input child y
  have hr' : (VectorReady.machine M).step^[s] ((VectorReady.machine M).initCfg input []) = c := hr
  have hhalt : c.state = (VectorReady.machine M).qHalt := by rw [← hr']; exact hout.1
  have hvc : c.cells (VectorReady.machine M).outTape =
      (VectorReady.machine M).tapeOf ((sign::x).map (VectorReady.machine M).bitSym) := by
    rw [← hr']; exact hout.2
  have hvh : c.head (VectorReady.machine M).outTape = 1 := by rw [← hr']; exact hhead
  have hroot : c.cells (VectorReady.machine M).inTape =
      fun p => PreprocessorAlphabet.encode (VectorReady.machine M)
        ((DescriptorSetup.machine.initCfg input []).cells 0 p) := by
    rw [← hr',FirstCoordinateInput.run_cells]
    exact (input_embed (VectorReady.machine M) input).symm
  obtain ⟨hc,hch,ht,hth⟩ := descriptors M input y child
  obtain ⟨t,htime,he⟩ := extract_run M c input [] s hr' hhalt
    ((DescriptorSetup.machine.initCfg input []).cells 0) (c.head (VectorReady.machine M).inTape)
    sign x y hroot rfl hvc hvh hc hch ht hth hx
  refine ⟨t,v,?_,hv,he⟩
  change s ≤ 193*n*q+11*T at hs
  dsimp only [q,y] at hs htime
  omega
