-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegrand_congr_branchPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:46.401853+00:00
-- url     : https://prove2.me/submissions/4343f083-c151-466a-9d6d-0a3827aacca8

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u v : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpoint : ∀ ts, h.branchPoint u ts = h.branchPoint v ts) :
    h.branchIntegrand u ρ = h.branchIntegrand v ρ := by
  funext ts
  rw [branchIntegrand_def, branchIntegrand_def, hpoint ts]
end BKAR.Forest.OrderedGrowth
