-- Prove2me | solution 1 for BitDFT.shared_alphabet_child_run_v2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T09:02:13.950363+00:00
-- url     : https://prove2.me/submissions/36a7c929-bea3-4c7a-a056-2bb881baf0a1

import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct

set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding

/-- The child stage runs in the common product alphabet with exact clock
    preservation, regardless of the data parked on the extra tapes. -/
theorem solution (A M : MultitapeTM)
    (extraCells : Fin (width A M) → ℕ → (BitDFT.SharedAlphabet.carrier A M).Sym)
    (extraHeads : Fin (width A M) → ℕ) (c : A.Cfg) (t : ℕ) :
    (left A M).step^[t]
      (BitDFT.TapeCountTransport.embed
        (BitDFT.TapeExtension.machine (BitDFT.AlphabetEmbedding.machine
          (BitDFT.SharedAlphabet.left A M)) (width A M - A.k))
        (width A M) (Nat.add_sub_of_le (Nat.le_max_left A.k M.k))
        (BitDFT.TapeExtension.embed
          (BitDFT.AlphabetEmbedding.machine (BitDFT.SharedAlphabet.left A M))
          (width A M - A.k)
          (fun i => extraCells (Fin.cast (Nat.add_sub_of_le (Nat.le_max_left A.k M.k)) i))
          (fun i => extraHeads (Fin.cast (Nat.add_sub_of_le (Nat.le_max_left A.k M.k)) i))
          (BitDFT.AlphabetEmbedding.embed (BitDFT.SharedAlphabet.left A M) c))) =
    BitDFT.TapeCountTransport.embed
      (BitDFT.TapeExtension.machine (BitDFT.AlphabetEmbedding.machine
        (BitDFT.SharedAlphabet.left A M)) (width A M - A.k))
      (width A M) (Nat.add_sub_of_le (Nat.le_max_left A.k M.k))
      (BitDFT.TapeExtension.embed
        (BitDFT.AlphabetEmbedding.machine (BitDFT.SharedAlphabet.left A M))
        (width A M - A.k)
        (fun i => extraCells (Fin.cast (Nat.add_sub_of_le (Nat.le_max_left A.k M.k)) i))
        (fun i => extraHeads (Fin.cast (Nat.add_sub_of_le (Nat.le_max_left A.k M.k)) i))
        (BitDFT.AlphabetEmbedding.embed (BitDFT.SharedAlphabet.left A M) (A.step^[t] c))) := by
  let E := BitDFT.AlphabetEmbedding.machine (BitDFT.SharedAlphabet.left A M)
  let r := width A M - A.k
  let h := Nat.add_sub_of_le (Nat.le_max_left A.k M.k)
  let padded := BitDFT.TapeExtension.machine E r
  let encoded := BitDFT.AlphabetEmbedding.embed (BitDFT.SharedAlphabet.left A M) c
  have hExt := (BitDFT.tape_extension_correct E r).1
    (fun i => extraCells (Fin.cast h i)) (fun i => extraHeads (Fin.cast h i)) encoded t
  have hAlpha := (BitDFT.alphabet_embedding_correct A (BitDFT.SharedAlphabet.carrier A M)
    (BitDFT.SharedAlphabet.left A M)).1 c t
  change (BitDFT.TapeCountTransport.machine padded (width A M) h).step^[t]
      (BitDFT.TapeCountTransport.embed padded (width A M) h
        (BitDFT.TapeExtension.embed E r
          (fun i => extraCells (Fin.cast h i))
          (fun i => extraHeads (Fin.cast h i)) encoded)) =
    BitDFT.TapeCountTransport.embed padded (width A M) h
      (BitDFT.TapeExtension.embed E r
        (fun i => extraCells (Fin.cast h i))
        (fun i => extraHeads (Fin.cast h i))
        (BitDFT.AlphabetEmbedding.embed (BitDFT.SharedAlphabet.left A M) (A.step^[t] c)))
  rw [BitDFT.tape_count_transport_correct padded (width A M) h
    (BitDFT.TapeExtension.embed E r
      (fun i => extraCells (Fin.cast h i))
      (fun i => extraHeads (Fin.cast h i)) encoded) t]
  rw [hExt,hAlpha]
