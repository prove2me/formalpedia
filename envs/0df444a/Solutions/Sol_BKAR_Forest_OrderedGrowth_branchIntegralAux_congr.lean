-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegralAux_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:18.218415+00:00
-- url     : https://prove2.me/submissions/9796baa2-5c6d-4c3c-a42b-3b72dfe60cd8

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (top : ℝ) (h : OrderedGrowth F order G)
    {u v : F.EdgeParam → ℝ} {ρ σ : (Edge V → ℝ) → ℝ}
    (hfg : ∀ ts, h.branchIntegrand u ρ ts = h.branchIntegrand v σ ts) :
    h.branchIntegralAux top u ρ = h.branchIntegralAux top v σ := by
  rw [branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top order hfg
end BKAR.Forest.OrderedGrowth
