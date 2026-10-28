-- Prove2me | solution 1 for BitDFT.shared_alphabet_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T22:13:14.972023+00:00
-- url     : https://prove2.me/submissions/30ff5f3b-430e-4ac4-826a-a07f6a0ffbb1

import Definitions.Def_BitDFT_SharedAlphabet
import Theorems.Thm_BitDFT_alphabet_embedding_correct

set_option autoImplicit false
open IntMul BitDFT.AlphabetEmbedding BitDFT.SharedAlphabet

/-- The product alphabet admits both component machines with their exact
    clocks and complete halting outputs preserved. -/
theorem solution (A M : MultitapeTM) :
    (∀ (c : A.Cfg) (t : ℕ),
      (machine (left A M)).step^[t]
          (BitDFT.AlphabetEmbedding.embed (left A M) c) =
        BitDFT.AlphabetEmbedding.embed (left A M) (A.step^[t] c)) ∧
    (∀ (x y : List Bool) (t : ℕ) (w : List Bool),
      A.HaltsWithOutput x y t w →
        (machine (left A M)).HaltsWithOutput x y t w) ∧
    (∀ (c : M.Cfg) (t : ℕ),
      (machine (right A M)).step^[t]
          (BitDFT.AlphabetEmbedding.embed (right A M) c) =
        BitDFT.AlphabetEmbedding.embed (right A M) (M.step^[t] c)) ∧
    (∀ (x y : List Bool) (t : ℕ) (w : List Bool),
      M.HaltsWithOutput x y t w →
        (machine (right A M)).HaltsWithOutput x y t w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (BitDFT.alphabet_embedding_correct A (carrier A M) (left A M)).1
  · exact (BitDFT.alphabet_embedding_correct A (carrier A M) (left A M)).2
  · exact (BitDFT.alphabet_embedding_correct M (carrier A M) (right A M)).1
  · exact (BitDFT.alphabet_embedding_correct M (carrier A M) (right A M)).2
