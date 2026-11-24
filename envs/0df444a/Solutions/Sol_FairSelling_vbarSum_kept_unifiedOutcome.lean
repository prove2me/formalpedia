-- Prove2me | solution 1 for FairSelling.vbarSum_kept_unifiedOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:49.430407+00:00
-- url     : https://prove2.me/submissions/6ed53b65-ffa3-4fe7-9986-0da07e9d0a73

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSSefx
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept i)
      = ∑ g ∈ (unifiedOutcome v p A F q).kept i, v i g := by
  classical
  refine Finset.sum_congr rfl (fun g hg => ?_)
  simp only [unifiedOutcome, Finset.mem_filter, not_lt] at hg
  exact max_eq_right hg.2
end FairSelling
