-- Prove2me | solution 1 for BraidsLinksMCG.thm_1_4_fadell_neuwirth_exact
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:20:19.078572+00:00
-- url     : https://prove2.me/submissions/97c9cc60-078b-469c-9feb-d2cbceda948a

import Theorems.Thm_BraidsLinksMCG_fadellNeuwirth_incl_injective
import Theorems.Thm_BraidsLinksMCG_fadellNeuwirth_range_eq_ker
import Theorems.Thm_BraidsLinksMCG_pureBraid_forget_section
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

theorem _root_.solution (n : ℕ) :
    Function.Injective (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)) ∧
      Function.Surjective (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)) ∧
      (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)).range =
        (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker := by
  refine ⟨BraidsLinksMCG.fadellNeuwirth_incl_injective n, ?_,
    BraidsLinksMCG.fadellNeuwirth_range_eq_ker n⟩
  obtain ⟨s, hs⟩ := BraidsLinksMCG.pureBraid_forget_section n
  intro x
  refine ⟨s x, ?_⟩
  have := congrArg (fun g => g x) hs
  simpa using this

#print axioms solution
