-- Prove2me | solution 1 for DeletionCode.MaximalRuns.run_length_le_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:21.147982+00:00
-- url     : https://prove2.me/submissions/6e67e56d-03a2-4f34-b940-d58190e52fc8

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
import Theorems.Thm_DeletionCode_MaximalRuns_constantOn_block
import Theorems.Thm_DeletionCode_UniqueRuns_constant_length_le


set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (word : List Bool) (k : ℕ)
    (hx : KUnique (listLetters word) word.length k)
    (pre suffix : List Bool) (rho : ℕ) (bit : Bool)
    (hword : word = pre ++ List.replicate rho bit ++ suffix) : rho ≤ k := by
  subst word
  apply constant_length_le k _ _ hx pre.length rho bit
  · simp only [List.length_append, List.length_replicate]
    omega
  · exact constantOn_block pre suffix rho bit
end DeletionCode.MaximalRuns
