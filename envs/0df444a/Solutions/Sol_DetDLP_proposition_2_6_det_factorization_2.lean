-- Prove2me | solution 2 for DetDLP.proposition_2_6_det_factorization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:44.150131+00:00
-- url     : https://prove2.me/submissions/74586d55-5bf8-4120-a7f2-554ce616f053
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_theorem_2_2_btn_contraction
import Theorems.Thm_DetDLP_lemma_2_3_mult_gadget
import Theorems.Thm_DetDLP_divisor_btn_parsimony_and_minfac
import Theorems.Thm_DetDLP_btn_parsimonious_count_and_stage1_cross_mul
import Theorems.Thm_DetDLP_factorization_tm_from_divisor_parsimony

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M out (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n) :=
  DetDLP.factorization_tm_from_divisor_parsimony
    DetDLP.theorem_2_2_btn_contraction
    DetDLP.lemma_2_3_mult_gadget
    DetDLP.divisor_btn_parsimony_and_minfac
    DetDLP.btn_parsimonious_count_and_stage1_cross_mul.1
