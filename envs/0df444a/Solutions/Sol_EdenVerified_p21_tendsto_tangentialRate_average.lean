-- Prove2me | solution 1 for EdenVerified.p21_tendsto_tangentialRate_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:31:21.391434+00:00
-- url     : https://prove2.me/submissions/01a113f6-aa3c-4d50-806d-544864082839

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_tangentialRate_average


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {s : ℝ} (hs : 0 ≤ s),
    Tendsto (fun t => (∫ τ in (0 : ℝ)..t,
      tangentialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (tangentialRate (limitingSquaredRadius s))) :=
  @Eden.tendsto_tangentialRate_average
end EdenVerified
