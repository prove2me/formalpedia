-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegral_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:19.187399+00:00
-- url     : https://prove2.me/submissions/1f702359-b034-479b-8259-ef6825695ae5

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_congr

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    {u v : F.EdgeParam → ℝ} {ρ σ : (Edge V → ℝ) → ℝ}
    (hfg : ∀ ts, h.branchIntegrand u ρ ts = h.branchIntegrand v σ ts) :
    h.branchIntegral u ρ = h.branchIntegral v σ :=
  h.branchIntegralAux_congr 1 hfg
end BKAR.Forest.OrderedGrowth
