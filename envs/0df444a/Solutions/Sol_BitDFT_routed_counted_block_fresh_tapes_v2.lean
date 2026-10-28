-- Prove2me | solution 1 for BitDFT.routed_counted_block_fresh_tapes_v2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T06:37:36.204499+00:00
-- url     : https://prove2.me/submissions/e6453114-c5fa-4022-82f2-46fdc5d1dce7

import Definitions.Def_BitDFT_RoutedCountedBlockFreshTapes
import Definitions.Def_BitDFT_CountedBlockOnMultiplierAlphabet
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run

set_option autoImplicit false
noncomputable section
open IntMul BitDFT BitDFT.RoutedCountedBlockFreshTapes


private theorem serializerStorageRun (M : MultitapeTM)
    (base : (CountedBlockOnMultiplierAlphabet.machine M).Cfg)
    (pre out x y : List Bool) (hx : val y + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (CountedBlockOnMultiplierAlphabet.machine M).step^[t]
        (CountedBlockOnMultiplierAlphabet.embed M base
          (AlphabetEmbedding.embed (CountedBlockOnMultiplierAlphabet.alphabetMap M)
            (CountedBlock.frame pre out x y y.reverse 0 .emit))) =
      CountedBlockOnMultiplierAlphabet.embed M base
        (AlphabetEmbedding.embed (CountedBlockOnMultiplierAlphabet.alphabetMap M)
          (CountedBlock.frame pre out x y y.reverse (val y+1) .halt)) := by
  obtain ⟨t, ht, hr⟩ := BitDFT.counted_block_correct pre out x y hx
  refine ⟨t, ht, ?_⟩
  rw [CountedBlockOnMultiplierAlphabet.run]
  rw [(BitDFT.alphabet_embedding_correct
    CountedBlockOnMultiplierAlphabet.sourceMachine M
    (CountedBlockOnMultiplierAlphabet.alphabetMap M)).1 _ t]
  exact congrArg
    (fun c => CountedBlockOnMultiplierAlphabet.embed M base
      (AlphabetEmbedding.embed (CountedBlockOnMultiplierAlphabet.alphabetMap M) c)) hr


theorem solution (M : MultitapeTM)
    (base : (host M).Cfg)
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ)
    (pre out x y : List Bool) (hx : val y + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (machine M).step^[t]
        (embed M base extraCells extraHeads
          (AlphabetEmbedding.embed
            (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
            (CountedBlock.frame pre out x y y.reverse 0 .emit))) =
      embed M base extraCells extraHeads
        (AlphabetEmbedding.embed
          (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
          (CountedBlock.frame pre out x y y.reverse (val y+1) .halt)) := by
  obtain ⟨t, ht, hrun⟩ :=
    serializerStorageRun (source M) base pre out x y hx
  refine ⟨t, ht, ?_⟩
  let r := (source M).k - 2
  let E := TapeExtension.machine (host M) r
  let he : E.inTape = E.inTape := rfl
  let c₀ := CountedBlockOnMultiplierAlphabet.embed (source M) base
    (AlphabetEmbedding.embed (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
      (CountedBlock.frame pre out x y y.reverse 0 .emit))
  let c₁ := CountedBlockOnMultiplierAlphabet.embed (source M) base
    (AlphabetEmbedding.embed (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
      (CountedBlock.frame pre out x y y.reverse (val y+1) .halt))
  have hext := (BitDFT.tape_extension_correct (host M) r).1
    extraCells extraHeads c₀ t
  rw [hrun] at hext
  have hperm := BitDFT.tape_permutation_run E
    (SerializerFreshTapeRouting.routing r)
    (by change SerializerFreshTapeRouting.routing r ⟨0,by omega⟩ = ⟨0,by omega⟩
        exact SerializerFreshTapeRouting.routing_input r)
    (TapeExtension.embed (host M) r extraCells extraHeads c₀) t
  rw [hext] at hperm
  simpa [machine, embed, r, E, c₀, c₁] using hperm

end
