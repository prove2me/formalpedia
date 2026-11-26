-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegral_congr_branchPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:23.181883+00:00
-- url     : https://prove2.me/submissions/c41162d8-0bba-4633-b5a9-620bf906eacf

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_congr

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
    h.branchIntegral u ρ = h.branchIntegral v ρ :=
  h.branchIntegral_congr
    (fun ts => by rw [branchIntegrand_def, branchIntegrand_def, hpoint ts])
end BKAR.Forest.OrderedGrowth
