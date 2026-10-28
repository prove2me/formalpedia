-- Prove2me | solution 1 for BitDFT.record_suffix_copy_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T20:11:22.481472+00:00
-- url     : https://prove2.me/submissions/cb820ea6-139b-473f-b2a6-1f869a9198c9

import Definitions.Def_BitDFT_RecordSuffixCopy
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct

namespace BitDFT.RecordSuffixCopy
open IntMul

end BitDFT.RecordSuffixCopy
open BitDFT.RecordSuffixCopy BitDFT.SuffixCopyTwoTape IntMul

theorem solution (M : MultitapeTM)
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
