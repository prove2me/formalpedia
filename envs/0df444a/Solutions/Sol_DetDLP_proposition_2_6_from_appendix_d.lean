-- Prove2me | solution 1 for DetDLP.proposition_2_6_from_appendix_d
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T07:22:32.085468+00:00
-- url     : https://prove2.me/submissions/993288fc-2a33-416d-8ab2-6a0f55d28921

import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_Machine
import Theorems.Thm_DetDLP_theorem_2_2_from_appendix_d
import Theorems.Thm_DetDLP_lemma_2_3_mult_gadget
import Theorems.Thm_DetDLP_divisor_btn_parsimony_and_minfac
import Theorems.Thm_DetDLP_btn_parsimonious_count_and_stage1_cross_mul
import Theorems.Thm_DetDLP_factorization_tm_from_divisor_parsimony

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution (hOAI : OpenAIAppendixDPremise) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M out (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n) :=
  DetDLP.factorization_tm_from_divisor_parsimony
    (DetDLP.theorem_2_2_from_appendix_d hOAI)
    DetDLP.lemma_2_3_mult_gadget
    DetDLP.divisor_btn_parsimony_and_minfac
    DetDLP.btn_parsimonious_count_and_stage1_cross_mul.1
