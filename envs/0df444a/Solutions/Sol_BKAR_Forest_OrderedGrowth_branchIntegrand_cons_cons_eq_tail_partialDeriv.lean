-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegrand_cons_cons_eq_tail_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:35.609164+00:00
-- url     : https://prove2.me/submissions/0edef3f9-be0c-437c-a80f-05284daaccb9

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_cons_cons
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
import Theorems.Thm_BKAR_mixedPartialList_append


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
    (step : EdgeExtension F F' e) (tail : OrderedGrowth F' order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts) =
      tail.branchIntegrand (step.extendParam u t) (partialDeriv e ρ) ts := by
  rw [branchIntegrand_cons_cons, branchIntegrand_def]
  rw [List.reverse_cons, mixedPartialList_append]
  rfl
end BKAR.Forest.OrderedGrowth
