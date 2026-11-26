-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegralAux_congr_branchPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:19.623751+00:00
-- url     : https://prove2.me/submissions/5fda408a-6e06-471b-a676-ffad71536056

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_congr

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (top : ℝ)
    (h : OrderedGrowth F order G) (u v : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ)
    (hpoint : ∀ ts, h.branchPoint u ts = h.branchPoint v ts) :
    h.branchIntegralAux top u ρ = h.branchIntegralAux top v ρ :=
  h.branchIntegralAux_congr top
    (fun ts => by rw [branchIntegrand_def, branchIntegrand_def, hpoint ts])
end BKAR.Forest.OrderedGrowth
