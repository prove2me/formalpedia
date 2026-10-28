-- Prove2me | solution 1 for BitDFT.shared_alphabet_multiplier_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T08:59:09.107646+00:00
-- url     : https://prove2.me/submissions/cdc45fc1-3484-447b-a888-f92ed00be672

import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct

set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding

/-- The multiplier stage runs in the common product alphabet with exact clock
    preservation, regardless of the data parked on the extra tapes. -/
theorem solution (A M : MultitapeTM)
    (extraCells : Fin (width A M) → ℕ → (BitDFT.SharedAlphabet.carrier A M).Sym)
    (extraHeads : Fin (width A M) → ℕ) (c : M.Cfg) (t : ℕ) :
    (right A M).step^[t] (rightConfig A M extraCells extraHeads c) =
      rightConfig A M extraCells extraHeads (M.step^[t] c) := by
  let E := BitDFT.AlphabetEmbedding.machine (BitDFT.SharedAlphabet.right A M)
  let r := width A M - M.k
  let h := Nat.add_sub_of_le (Nat.le_max_right A.k M.k)
  let padded := BitDFT.TapeExtension.machine E r
  let encoded := BitDFT.AlphabetEmbedding.embed (BitDFT.SharedAlphabet.right A M) c
  have hExt := (BitDFT.tape_extension_correct E r).1
    (fun i => extraCells (Fin.cast h i)) (fun i => extraHeads (Fin.cast h i)) encoded t
  have hAlpha := (BitDFT.alphabet_embedding_correct M (BitDFT.SharedAlphabet.carrier A M)
    (BitDFT.SharedAlphabet.right A M)).1 c t
  change (BitDFT.TapeCountTransport.machine padded (width A M) h).step^[t]
      (BitDFT.TapeCountTransport.embed padded (width A M) h
        (BitDFT.TapeExtension.embed E r
          (fun i => extraCells (Fin.cast h i))
          (fun i => extraHeads (Fin.cast h i)) encoded)) =
    BitDFT.TapeCountTransport.embed padded (width A M) h
      (BitDFT.TapeExtension.embed E r
        (fun i => extraCells (Fin.cast h i))
        (fun i => extraHeads (Fin.cast h i))
        (BitDFT.AlphabetEmbedding.embed (BitDFT.SharedAlphabet.right A M) (M.step^[t] c)))
  rw [BitDFT.tape_count_transport_correct padded (width A M) h
    (BitDFT.TapeExtension.embed E r
      (fun i => extraCells (Fin.cast h i))
      (fun i => extraHeads (Fin.cast h i)) encoded) t]
  rw [hExt,hAlpha]
