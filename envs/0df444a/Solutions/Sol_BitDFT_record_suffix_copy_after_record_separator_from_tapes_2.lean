-- Prove2me | solution 2 for BitDFT.record_suffix_copy_after_record_separator_from_tapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T20:47:20.484678+00:00
-- url     : https://prove2.me/submissions/e408281c-d5a1-4120-9c78-f963c142d457

import Definitions.Def_BitDFT_RecordSuffixCopy
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_signed_block_final_slots

namespace BitDFT.RecordSuffixCopy
open IntMul

end BitDFT.RecordSuffixCopy
open BitDFT.RecordSuffixCopy BitDFT.SuffixCopyTwoTape IntMul
namespace Aux_record_suffix_copy_from_tapes
open BitDFT.RecordSuffixCopy BitDFT.SuffixCopyTwoTape IntMul

theorem copy_solution (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    (routed M).step^[rest.length+1]
      (embed M cells heads rootCells rootHead
        (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))) =
      embed M cells heads rootCells rootHead
        (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
          (pre.length+rest.length+1)) := by
  rw [run_embed, BitDFT.two_tape_suffix_copy_correct]

private theorem host_ge_three (M : MultitapeTM) : 3 ≤ (host M).k := by
  change 3 ≤ 5 + (M.k + 3)
  omega

private theorem inverse_routing_one (M : MultitapeTM) :
    (routing M).symm (sourceTape M) =
      (⟨1, by have := host_ge_three M; omega⟩ : Fin (host M).k) := by
  apply (routing M).injective
  simpa using (routing_one M).symm

private theorem inverse_routing_zero (M : MultitapeTM) :
    (routing M).symm (host M).inTape =
      (⟨0, by have := host_ge_three M; omega⟩ : Fin (host M).k) := by
  apply (routing M).injective
  simpa [MultitapeTM.inTape] using (routing_zero M).symm

private theorem raw_index_zero (M : MultitapeTM) :
    Fin.cast (extension_count M).symm ((routing M).symm (host M).inTape) =
      (⟨0, by have hg := host_ge_three M; change 0 < 3 + ((host M).k - 3); omega⟩ :
        Fin ((relocated M).k + ((host M).k - 3))) := by
  apply Fin.ext
  simp only [Fin.val_cast]
  exact congrArg Fin.val (inverse_routing_zero M)

private theorem raw_index_one (M : MultitapeTM) :
    Fin.cast (extension_count M).symm ((routing M).symm (sourceTape M)) =
      (⟨1, by have hg := host_ge_three M; change 1 < 3 + ((host M).k - 3); omega⟩ :
        Fin ((relocated M).k + ((host M).k - 3))) := by
  apply Fin.ext
  simp only [Fin.val_cast, Equiv.apply_symm_apply]
  exact congrArg Fin.val (inverse_routing_one M)

private theorem inverse_routing_two (M : MultitapeTM) :
    (routing M).symm (host M).outTape =
      (⟨2, by have := host_ge_three M; omega⟩ : Fin (host M).k) := by
  apply (routing M).injective
  simpa using (routing_two M).symm

private theorem raw_index_two (M : MultitapeTM) :
    Fin.cast (extension_count M).symm ((routing M).symm (host M).outTape) =
      (⟨2, by have hg := host_ge_three M; change 2 < 3 + ((host M).k - 3); omega⟩ :
        Fin ((relocated M).k + ((host M).k - 3))) := by
  apply Fin.ext
  simp only [Fin.val_cast]
  exact congrArg Fin.val (inverse_routing_two M)

theorem source_frame (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).cells (sourceTape M) =
        (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
          ((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym ++ [TapeCopy.Sym.sep]) p)) := by
  simp only [embed,BitDFT.TapePermutation.embed,BitDFT.TapeCountTransport.embed]
  rw [raw_index_one]
  have hlt : 1 < (relocated M).k := by have := (relocated M).two_le_k; omega
  simp [BitDFT.TapeExtension.embed,BitDFT.WorkRelocation.embed,
    BitDFT.WorkRelocation.innerTape,BitDFT.AlphabetEmbedding.embed,
    alphabetMap,BitDFT.SuffixCopyTwoTape.frame,List.map_append,List.append_assoc,hlt]
  rfl

theorem output_frame (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).cells (host M).outTape =
        (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
          (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)) := by
  simp only [embed,BitDFT.TapePermutation.embed,BitDFT.TapeCountTransport.embed]
  rw [raw_index_two]
  have hlt : 2 < (relocated M).k := by change 2 < 3; omega
  simp [BitDFT.TapeExtension.embed,BitDFT.WorkRelocation.embed,
    BitDFT.WorkRelocation.innerTape,BitDFT.AlphabetEmbedding.embed,
    alphabetMap,BitDFT.SuffixCopyTwoTape.frame,hlt]
  rfl

theorem source_head (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).head
        (sourceTape M) = pre.length+1 := by
  simp only [embed,BitDFT.TapePermutation.embed,BitDFT.TapeCountTransport.embed]
  rw [raw_index_one]
  have hlt : 1 < (relocated M).k := by have := (relocated M).two_le_k; omega
  simp [BitDFT.TapeExtension.embed,BitDFT.WorkRelocation.embed,
    BitDFT.WorkRelocation.innerTape,BitDFT.AlphabetEmbedding.embed,
    BitDFT.SuffixCopyTwoTape.frame,hlt]

theorem output_head (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).head
        (host M).outTape = out.length+1 := by
  simp only [embed,BitDFT.TapePermutation.embed,BitDFT.TapeCountTransport.embed]
  rw [raw_index_two]
  have hlt : 2 < (relocated M).k := by change 2 < 3; omega
  simp [BitDFT.TapeExtension.embed,BitDFT.WorkRelocation.embed,
    BitDFT.WorkRelocation.innerTape,BitDFT.AlphabetEmbedding.embed,
    BitDFT.SuffixCopyTwoTape.frame,hlt]

theorem input_frame_cells (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).cells
        (host M).inTape = rootCells := by
  simp only [embed,BitDFT.TapePermutation.embed,BitDFT.TapeCountTransport.embed]
  rw [raw_index_zero]
  have hlt : 0 < (relocated M).k := by have := (relocated M).two_le_k; omega
  simp [BitDFT.TapeExtension.embed,BitDFT.WorkRelocation.embed,hlt]

theorem input_frame_head (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).head
        (host M).inTape = rootHead := by
  simp only [embed,BitDFT.TapePermutation.embed,BitDFT.TapeCountTransport.embed]
  rw [raw_index_zero]
  have hlt : 0 < (relocated M).k := by have := (relocated M).two_le_k; omega
  simp [BitDFT.TapeExtension.embed,BitDFT.WorkRelocation.embed,hlt]

theorem parked_tape (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) (i : Fin (host M).k)
    (hi0 : i ≠ (host M).inTape) (hi1 : i ≠ (host M).outTape)
    (his : i ≠ sourceTape M) :
    (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).cells i = cells i ∧
    (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).head i = heads i := by
  have hlarge : 3 ≤ ((routing M).symm i).val := by
    by_contra h
    have hlt : ((routing M).symm i).val < 3 := by omega
    interval_cases hval : ((routing M).symm i).val <;>
      first
      | have hidx : (routing M).symm i = ⟨0, by have := host_ge_three M; omega⟩ := by
          apply Fin.ext; simpa using hval
        have : i = (host M).inTape := by
          calc
            i = routing M ((routing M).symm i) := (Equiv.apply_symm_apply (routing M) i).symm
            _ = (host M).inTape := by rw [hidx]; exact routing_zero M
        exact (hi0 this).elim
      | have hidx : (routing M).symm i = ⟨1, by have := host_ge_three M; omega⟩ := by
          apply Fin.ext; simpa using hval
        have : i = sourceTape M := by
          calc
            i = routing M ((routing M).symm i) := (Equiv.apply_symm_apply (routing M) i).symm
            _ = sourceTape M := by rw [hidx]; exact routing_one M
        exact (his this).elim
      | have hidx : (routing M).symm i = ⟨2, by have := host_ge_three M; omega⟩ := by
          apply Fin.ext; simpa using hval
        have : i = (host M).outTape := by
          calc
            i = routing M ((routing M).symm i) := (Equiv.apply_symm_apply (routing M) i).symm
            _ = (host M).outTape := by rw [hidx]; exact routing_two M
        exact (hi1 this).elim
  constructor
  · simp only [embed,BitDFT.TapePermutation.embed,BitDFT.TapeCountTransport.embed]
    simp [BitDFT.TapeExtension.embed,Fin.val_cast,hlarge]
  · simp only [embed,BitDFT.TapePermutation.embed,BitDFT.TapeCountTransport.embed]
    have hround : routing M (Fin.cast (extension_count M)
        (Fin.cast (extension_count M).symm ((routing M).symm i))) = i := by
      apply Fin.ext
      simp [Fin.val_cast,Equiv.apply_symm_apply]
    simp [BitDFT.TapeExtension.embed,Fin.val_cast,hlarge,hround]

private theorem suffix_tape_append (w : List TapeCopy.Sym) (a : TapeCopy.Sym) :
    Function.update (BitDFT.SuffixCopyTwoTape.machine.tapeOf w) (w.length+1) a =
      BitDFT.SuffixCopyTwoTape.machine.tapeOf (w++[a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = w.length
    · subst p
      simp [MultitapeTM.tapeOf,List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p+1 ≠ w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem encoded_tape_append (M : MultitapeTM) (w : List TapeCopy.Sym) :
    Function.update
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf w p))
      (w.length+1) (host M).sep =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf (w++[TapeCopy.Sym.sep]) p)) := by
  funext p
  rw [← suffix_tape_append w TapeCopy.Sym.sep]
  by_cases hp : p = w.length+1
  · subst p
    simp [encode]
  · simp [Function.update, hp]

private theorem tape_copy_blank_ne_start :
    BitDFT.SuffixCopyTwoTape.machine.blank ≠
      BitDFT.SuffixCopyTwoTape.machine.startSym := by
  have h := BitDFT.SuffixCopyTwoTape.machine.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at h
  aesop

private theorem word_no_start (w : List TapeCopy.Sym)
    (hw : ∀ s ∈ w, s ≠ TapeCopy.Sym.start) (p : ℕ) :
    BitDFT.SuffixCopyTwoTape.machine.tapeOf w (p+1) ≠ TapeCopy.Sym.start := by
  rw [MultitapeTM.tapeOf]
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ hp]
    exact hw _ (List.getElem_mem hp)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact tape_copy_blank_ne_start

private theorem encoded_copy_symbol_ne_start (M : MultitapeTM)
    (s : TapeCopy.Sym) (hs : s ≠ TapeCopy.Sym.start) :
    encode M s ≠ (host M).startSym := by
  intro he
  apply hs
  apply (alphabetMap M).encode.injective
  change encode M s = encode M TapeCopy.Sym.start
  rw [he]
  rfl

private theorem cfg_ext_early {N : MultitapeTM} (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem copy_tape_embed (M : MultitapeTM) (w : List TapeCopy.Sym) :
    (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf w p)) =
      (host M).tapeOf (w.map (encode M)) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf,encode]
  | succ p =>
    simp only [MultitapeTM.tapeOf,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases h : w[p]? <;> simp [h,encode]

private theorem copy_bits_embed (M : MultitapeTM) (bits : List Bool) :
    (bits.map BitDFT.SuffixCopyTwoTape.machine.bitSym).map (encode M) =
      bits.map (host M).bitSym := by
  rw [List.map_map]
  congr 1
  funext b
  cases b <;> rfl

theorem first_coordinate_record_layout (M : MultitapeTM)
    (c : (BitDFT.VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (sign : Bool) (x y : List Bool)
    (hx : IntMul.val y+1 ≤ x.length) :
    (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        ((sign::x.take (IntMul.val y+1)).map
          BitDFT.SuffixCopyTwoTape.machine.bitSym) p)) ∧
    (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).head
      (sourceTape M) = ((sign::x.take (IntMul.val y+1)).map
        BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1 := by
  have hslots := BitDFT.signed_block_final_slots (BitDFT.VectorReady.machine M) M.k
    (BitDFT.FirstCoordinate.start M c).cells (BitDFT.FirstCoordinate.start M c).head
    rootCells rootHead [] [] sign x y
  rcases hslots with ⟨_,_,hrecord,hhead,_,_,_,_⟩
  constructor
  · change (BitDFT.SignedBlockPlacement.embed (BitDFT.VectorReady.machine M) M.k
      (BitDFT.FirstCoordinate.start M c).cells (BitDFT.FirstCoordinate.start M c).head
      (BitDFT.WorkRelocation.embed BitDFT.SignedBlock.machine rootCells rootHead
        (BitDFT.SignedBlock.final [] [] sign x y))).cells
      (BitDFT.SignedBlockPlacement.scratchTape M.k) = _
    rw [hrecord,copy_tape_embed,copy_bits_embed]
    rfl
  · change (BitDFT.SignedBlockPlacement.embed (BitDFT.VectorReady.machine M) M.k
      (BitDFT.FirstCoordinate.start M c).cells (BitDFT.FirstCoordinate.start M c).head
      (BitDFT.WorkRelocation.embed BitDFT.SignedBlock.machine rootCells rootHead
        (BitDFT.SignedBlock.final [] [] sign x y))).head
      (BitDFT.SignedBlockPlacement.scratchTape M.k) = _
    rw [hhead]
    simp [List.length_map]
    omega

theorem rewind_record_tape_to_start (M : MultitapeTM)
    (b : (host M).Cfg) (pre rest : List Bool)
    (hsource : b.cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym) ++ [TapeCopy.Sym.sep]) p)))
    (hhead : b.head (sourceTape M) = ((pre++rest).map
      BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1) :
    (BitDFT.RewindTape.machine (host M) (sourceTape M)).step^[
      (((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym).length+2)]
      ⟨false,b.cells,b.head⟩ =
      BitDFT.RewindTape.frame (host M) (sourceTape M) b true 1 := by
  have hinit : (⟨false,b.cells,b.head⟩ :
      (BitDFT.RewindTape.machine (host M) (sourceTape M)).Cfg) =
      BitDFT.RewindTape.frame (host M) (sourceTape M) b false
        (((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1) := by
    apply cfg_ext_early
    · rfl
    · rfl
    · funext i
      by_cases hi : i = sourceTape M
      · subst i
        simp [BitDFT.RewindTape.frame,Function.update,hhead]
      · simp [BitDFT.RewindTape.frame,Function.update,hi]
  rw [hinit]
  apply BitDFT.rewind_tape_correct
  · rw [hsource]
    simp [MultitapeTM.tapeOf,encode]
  · intro p hp
    cases p with
    | zero => omega
    | succ p =>
      rw [hsource]
      have hw : ∀ s ∈
          (((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym) ++ [TapeCopy.Sym.sep]),
          s ≠ TapeCopy.Sym.start := by
        intro s hs
        simp only [List.mem_append,List.mem_map,List.mem_singleton] at hs
        rcases hs with ⟨b,_,rfl⟩ | rfl
        · cases b <;> decide
        · decide
      exact encoded_copy_symbol_ne_start M _ (word_no_start _ hw p)

theorem first_coordinate_record_rewind (M : MultitapeTM)
    (c : (BitDFT.VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (sign : Bool) (x y : List Bool)
    (hx : IntMul.val y+1 ≤ x.length) :
    let record := (sign::x.take (IntMul.val y+1))
    let b := BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y
    let post : (host M).Cfg :=
      ⟨b.state,
        Function.update b.cells (sourceTape M)
          (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep),
        b.head⟩
    (BitDFT.RewindTape.machine (host M) (sourceTape M)).step^[
      ((record.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length+2)]
      ⟨false,post.cells,post.head⟩ =
      BitDFT.RewindTape.frame (host M) (sourceTape M) post true 1 := by
  dsimp only
  let record := sign::x.take (IntMul.val y+1)
  let b := BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y
  let post : (host M).Cfg :=
    ⟨b.state,
      Function.update b.cells (sourceTape M)
        (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep),
      b.head⟩
  obtain ⟨hrecord,hhead⟩ := first_coordinate_record_layout M c rootCells rootHead sign x y hx
  have hsource : post.cells (sourceTape M) = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        ((record.map BitDFT.SuffixCopyTwoTape.machine.bitSym) ++ [TapeCopy.Sym.sep]) p) := by
    dsimp only [post]
    change (if sourceTape M = sourceTape M then
      Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep
      else b.cells (sourceTape M)) = _
    simp only [if_pos rfl]
    rw [hrecord,hhead]
    exact encoded_tape_append M (record.map BitDFT.SuffixCopyTwoTape.machine.bitSym)
  have hhead' : post.head (sourceTape M) =
      (record.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1 := by
    change b.head (sourceTape M) = _
    simpa [record] using hhead
  simpa [record] using
    (rewind_record_tape_to_start M post [] record hsource hhead')

theorem workspace_match_after_separator (M : MultitapeTM)
    (b : (host M).Cfg) (pre rest out : List Bool)
    (hsource : b.cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        ((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (hsourceHead : b.head (sourceTape M) = ((pre++rest).map
      BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1)
    (houtput : b.cells (host M).outTape =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (houtputHead : b.head (host M).outTape = out.length+1) :
    Function.update b.cells (sourceTape M)
      (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep) =
        (embed M b.cells b.head (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.frame (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .copy
            (pre++rest) out (pre.length+1))).cells := by
  let w := (pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym
  have hupdate : Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf (w++[TapeCopy.Sym.sep]) p)) := by
    rw [hsourceHead,hsource]
    exact encoded_tape_append M w
  funext i
  by_cases his : i = sourceTape M
  · subst i
    funext p
    change (if sourceTape M = sourceTape M then
        Function.update (b.cells (sourceTape M)) (b.head (sourceTape M))
          (host M).sep else b.cells (sourceTape M)) p = _
    rw [hupdate, source_frame]
    simp [w, List.map_append, List.append_assoc]
  · by_cases hiout : i = (host M).outTape
    · subst i
      funext p
      simp [Function.update,his,houtput]
      rw [output_frame]
    · by_cases hiin : i = (host M).inTape
      · subst i
        funext p
        simp [Function.update,his]
        rw [input_frame_cells]
      · have hpark := (parked_tape M b.cells b.head
          (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.machine.initCfg [] [])
          pre rest out i hiin hiout his).1
        simpa [his,hiout,hiin,Function.update] using hpark.symm

private def asControlCfg (M : MultitapeTM) (c : (routed M).Cfg) : (control M).machine.Cfg :=
  ⟨c.state,c.cells,c.head⟩

private theorem control_step_simulation (M : MultitapeTM) (c : (routed M).Cfg) :
    (control M).machine.step (asControlCfg M c) = asControlCfg M ((routed M).step c) := by
  cases c
  rfl

private theorem control_run_simulation (M : MultitapeTM) (c : (routed M).Cfg) (t : ℕ) :
    (control M).machine.step^[t] (asControlCfg M c) =
      asControlCfg M ((routed M).step^[t] c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply, control_step_simulation]
      simpa [Function.iterate_succ_apply] using ih ((routed M).step c)

private theorem cfg_ext {N : MultitapeTM} (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem outer_handoff_step {N : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller N)
    (c : P.machine.Cfg) (h : c.state = P.exit) :
    (BitDFT.MachineSequence.sequence P Q).machine.step
      (BitDFT.MachineSequence.leftCfg P Q c) =
      BitDFT.MachineSequence.rightCfg P Q (BitDFT.MachineSequence.handoff P Q c) := by
  apply cfg_ext
  · simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,
      BitDFT.MachineSequence.leftCfg,BitDFT.MachineSequence.rightCfg,
      BitDFT.MachineSequence.handoff,h]
  · funext i
    simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,
      BitDFT.MachineSequence.leftCfg,BitDFT.MachineSequence.rightCfg,
      BitDFT.MachineSequence.handoff,h]
  · funext i
    simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,
      BitDFT.MachineSequence.leftCfg,BitDFT.MachineSequence.rightCfg,
      BitDFT.MachineSequence.handoff,h]

private theorem outer_left_step {N : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller N)
    (c : P.machine.Cfg) (h : c.state ≠ P.exit) :
    (BitDFT.MachineSequence.sequence P Q).machine.step
      (BitDFT.MachineSequence.leftCfg P Q c) =
      BitDFT.MachineSequence.leftCfg P Q (P.machine.step c) := by
  apply cfg_ext
  · simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,
      BitDFT.MachineSequence.leftCfg,h]
  · funext i
    simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,
      BitDFT.MachineSequence.leftCfg,h]
  · funext i
    simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,
      BitDFT.MachineSequence.leftCfg,h]

private theorem outer_right_step {N : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller N) (c : Q.machine.Cfg) :
    (BitDFT.MachineSequence.sequence P Q).machine.step
      (BitDFT.MachineSequence.rightCfg P Q c) =
      BitDFT.MachineSequence.rightCfg P Q (Q.machine.step c) := by
  apply cfg_ext
  · simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,BitDFT.MachineSequence.rightCfg]
  · funext i
    simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,BitDFT.MachineSequence.rightCfg]
  · funext i
    simp [MultitapeTM.step,BitDFT.MachineSequence.sequence,BitDFT.MachineSequence.rightCfg]

private theorem outer_right_run {N : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller N) (c : Q.machine.Cfg) (t : ℕ) :
    (BitDFT.MachineSequence.sequence P Q).machine.step^[t]
      (BitDFT.MachineSequence.rightCfg P Q c) =
      BitDFT.MachineSequence.rightCfg P Q (Q.machine.step^[t] c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply,outer_right_step]
      simpa [Function.iterate_succ_apply] using ih (Q.machine.step c)

theorem after_separator_handoff (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    let initial := embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+2]
      (BitDFT.MachineSequence.leftCfg P Q ⟨P.exit,initial.cells,initial.head⟩) =
      BitDFT.MachineSequence.rightCfg P Q
        ⟨(embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).state,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).cells,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).head⟩ := by
  dsimp only
  let initial := embed M cells heads rootCells rootHead
    (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))
  let parent : (BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)).machine.Cfg :=
    ⟨(BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)).exit,initial.cells,initial.head⟩
  have hh : BitDFT.MachineSequence.handoff
      (BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
        (BitDFT.RecordTerminator.control M)) (control M) parent = asControlCfg M initial := by
    apply cfg_ext
    · rfl
    · rfl
    · rfl
  rw [Function.iterate_succ_apply,outer_handoff_step _ _ parent rfl,hh,
    outer_right_run,control_run_simulation,copy_solution]
  rfl

theorem after_record_separator (M : MultitapeTM)
    (b : (host M).Cfg)
    (hstate : b.state = (host M).qHalt)
    (hblank : b.cells (sourceTape M) (b.head (sourceTape M)) = (host M).blank)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool)
    (hworkspace : Function.update b.cells (sourceTape M)
      (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep) =
        (embed M cells heads rootCells rootHead
          (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).cells)
    (hheads : b.head = (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).head) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+4]
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) =
      BitDFT.MachineSequence.rightCfg P Q
        ⟨(embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).state,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).cells,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).head⟩ := by
  dsimp only
  let P0 := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
    (BitDFT.RecordTerminator.control M)
  let Q := control M
  let outer := BitDFT.MachineSequence.sequence P0 Q
  let innerStart := BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
    (BitDFT.RecordTerminator.control M) b
  let initial := embed M cells heads rootCells rootHead
    (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))
  let post : P0.machine.Cfg := ⟨.inr true,
    Function.update b.cells (sourceTape M)
      (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep), b.head⟩
  have h0 : innerStart.state ≠ P0.exit := by
    simp [innerStart,P0,BitDFT.MachineSequence.leftCfg,BitDFT.MachineSequence.sequence]
  have hnative :
      Sum.inr (Sum.inr BitDFT.SignedBlock.blockControl.exit) =
        (BitDFT.MachineSequence.native (BitDFT.RecordTerminator.storage M)).exit := rfl
  have h1 : (P0.machine.step innerStart).state ≠ P0.exit := by
    simp [innerStart,P0,BitDFT.MachineSequence.leftCfg,BitDFT.MachineSequence.sequence,
      MultitapeTM.step,BitDFT.RecordTerminator.control,host,
      BitDFT.MachineSequence.native,hstate,hnative]
  have outer_first := outer_left_step P0 Q innerStart h0
  have outer_second := outer_left_step P0 Q (P0.machine.step innerStart) h1
  have hinner := BitDFT.record_terminator_sequence_step M b hstate hblank
  have htwo : outer.machine.step^[2]
      (BitDFT.MachineSequence.leftCfg P0 Q innerStart) =
        BitDFT.MachineSequence.leftCfg P0 Q post := by
    calc
      outer.machine.step^[2] (BitDFT.MachineSequence.leftCfg P0 Q innerStart) =
          outer.machine.step (outer.machine.step
            (BitDFT.MachineSequence.leftCfg P0 Q innerStart)) := by
              norm_num [Function.iterate_succ_apply']
      _ = outer.machine.step
            (BitDFT.MachineSequence.leftCfg P0 Q (P0.machine.step innerStart)) := by
              rw [outer_first]
      _ = BitDFT.MachineSequence.leftCfg P0 Q
            (P0.machine.step (P0.machine.step innerStart)) := by
              rw [outer_second]
      _ = BitDFT.MachineSequence.leftCfg P0 Q post := by
              have hinner' : P0.machine.step^[2] innerStart = post := by
                change P0.machine.step (P0.machine.step innerStart) = post
                simpa [P0,post,host,sourceTape,innerStart,BitDFT.RecordTerminator.machine,
                  BitDFT.RecordTerminator.storage,BitDFT.RecordTerminator.control,
                  BitDFT.MachineSequence.rightCfg] using hinner
              have hinner'' : P0.machine.step (P0.machine.step innerStart) = post := by
                simpa [Function.iterate_succ_apply'] using hinner'
              exact congrArg (BitDFT.MachineSequence.leftCfg P0 Q) hinner''
  have hpost : post = ⟨P0.exit,initial.cells,initial.head⟩ := by
    apply cfg_ext
    · rfl
    · exact hworkspace
    · exact hheads
  calc
    outer.machine.step^[rest.length+4]
        (BitDFT.MachineSequence.leftCfg P0 Q innerStart) =
      outer.machine.step^[rest.length+2]
        (outer.machine.step^[2] (BitDFT.MachineSequence.leftCfg P0 Q innerStart)) := by
          rw [show rest.length+4 = (rest.length+2)+2 by omega,Function.iterate_add_apply]
    _ = outer.machine.step^[rest.length+2] (BitDFT.MachineSequence.leftCfg P0 Q post) := by rw [htwo]
    _ = outer.machine.step^[rest.length+2]
        (BitDFT.MachineSequence.leftCfg P0 Q ⟨P0.exit,initial.cells,initial.head⟩) := by rw [hpost]
    _ = BitDFT.MachineSequence.rightCfg P0 Q
        ⟨(embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).state,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).cells,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).head⟩ := by
          simpa [asControlCfg] using
            after_separator_handoff M cells heads rootCells rootHead base pre rest out

theorem after_record_separator_from_tapes (M : MultitapeTM)
    (b : (host M).Cfg)
    (hstate : b.state = (host M).qHalt)
    (hblank : b.cells (sourceTape M) (b.head (sourceTape M)) = (host M).blank)
    (pre rest out : List Bool)
    (hsource : b.cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        ((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (hsourceHead : b.head (sourceTape M) = ((pre++rest).map
      BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1)
    (houtput : b.cells (host M).outTape =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (houtputHead : b.head (host M).outTape = out.length+1)
    (hheads : b.head = (embed M b.cells b.head
      (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
      (BitDFT.SuffixCopyTwoTape.frame
        (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .copy
        (pre++rest) out (pre.length+1))).head) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+4]
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) =
      BitDFT.MachineSequence.rightCfg P Q
        ⟨(embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).state,
          (embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).cells,
          (embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).head⟩ := by
  apply after_record_separator M b hstate hblank b.cells b.head
    (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
    (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) pre rest out
  · exact workspace_match_after_separator M b pre rest out hsource hsourceHead houtput houtputHead
  · exact hheads

end Aux_record_suffix_copy_from_tapes

theorem solution (M : MultitapeTM)
    (b : (host M).Cfg)
    (hstate : b.state = (host M).qHalt)
    (hblank : b.cells (sourceTape M) (b.head (sourceTape M)) = (host M).blank)
    (pre rest out : List Bool)
    (hsource : b.cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        ((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (hsourceHead : b.head (sourceTape M) = ((pre++rest).map
      BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1)
    (houtput : b.cells (host M).outTape =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (houtputHead : b.head (host M).outTape = out.length+1)
    (hheads : b.head = (embed M b.cells b.head
      (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
      (BitDFT.SuffixCopyTwoTape.frame
        (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .copy
        (pre++rest) out (pre.length+1))).head) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+4]
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) =
      BitDFT.MachineSequence.rightCfg P Q
        ⟨(embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).state,
          (embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).cells,
          (embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).head⟩ := by
  apply Aux_record_suffix_copy_from_tapes.after_record_separator_from_tapes <;> assumption
