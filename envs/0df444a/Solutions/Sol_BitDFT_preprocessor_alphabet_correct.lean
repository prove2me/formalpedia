-- Prove2me | solution 1 for BitDFT.preprocessor_alphabet_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:57:03.756356+00:00
-- url     : https://prove2.me/submissions/b3811a77-c8b2-4b11-a429-35ca8f1d74d6

import Definitions.Def_BitDFT_PreprocessorAlphabet
import Theorems.Thm_BitDFT_request_preprocessor_correct
import Theorems.Thm_BitDFT_alphabet_embedding_correct

open BitDFT IntMul

theorem solution (N : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    Computes (PreprocessorAlphabet.machine N) (requestedInput b U) (fourierInput (guardPrecision n b) U)
      (27 * (n : ℝ) * (guardPrecision n b : ℝ)) := by
  obtain ⟨t,ht,hr⟩ := BitDFT.request_preprocessor_correct n b hn hb U
  refine ⟨t,ht,?_⟩
  exact (BitDFT.alphabet_embedding_correct RewriteInput.machine N (PreprocessorAlphabet.alphabetMap N)).2
    (requestedInput b U) [] t (fourierInput (guardPrecision n b) U) hr
