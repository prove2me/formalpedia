-- Prove2me | solution 1 for BitDFT.counted_block_correct_on_multiplier_alphabet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T04:48:28.26277+00:00
-- url     : https://prove2.me/submissions/6f8a1700-c2d0-435f-9ed1-c2388fdd751f

import Definitions.Def_BitDFT_CountedBlockOnMultiplierAlphabet
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_alphabet_embedding_correct

set_option autoImplicit false
open IntMul

theorem solution
    (M : MultitapeTM)
    (base : (BitDFT.CountedBlockOnMultiplierAlphabet.machine M).Cfg)
    (pre out x y : List Bool) (hx : val y + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (BitDFT.CountedBlockOnMultiplierAlphabet.machine M).step^[t]
        (BitDFT.CountedBlockOnMultiplierAlphabet.embed M base
          (BitDFT.AlphabetEmbedding.embed
            (BitDFT.CountedBlockOnMultiplierAlphabet.alphabetMap M)
            (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit))) =
      BitDFT.CountedBlockOnMultiplierAlphabet.embed M base
        (BitDFT.AlphabetEmbedding.embed
          (BitDFT.CountedBlockOnMultiplierAlphabet.alphabetMap M)
          (BitDFT.CountedBlock.frame pre out x y y.reverse (val y+1) .halt)) := by
  obtain ⟨t, ht, hr⟩ := BitDFT.counted_block_correct pre out x y hx
  refine ⟨t, ht, ?_⟩
  rw [BitDFT.CountedBlockOnMultiplierAlphabet.run]
  rw [(BitDFT.alphabet_embedding_correct
    BitDFT.CountedBlockOnMultiplierAlphabet.sourceMachine M
    (BitDFT.CountedBlockOnMultiplierAlphabet.alphabetMap M)).1 _ t]
  exact congrArg
    (fun c => BitDFT.CountedBlockOnMultiplierAlphabet.embed M base
      (BitDFT.AlphabetEmbedding.embed
        (BitDFT.CountedBlockOnMultiplierAlphabet.alphabetMap M) c)) hr
