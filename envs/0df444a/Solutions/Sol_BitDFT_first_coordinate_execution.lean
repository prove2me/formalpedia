-- Prove2me | solution 1 for BitDFT.first_coordinate_execution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:02:27.933891+00:00
-- url     : https://prove2.me/submissions/e95bddd4-fe30-4675-8b82-583b3693a152

import Theorems.Thm_BitDFT_extraction_ready
import Theorems.Thm_BitDFT_signed_block_placement_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Definitions.Def_BitDFT_FirstCoordinate
import Theorems.Thm_BitDFT_signed_block_initial_match

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
theorem solution (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
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
