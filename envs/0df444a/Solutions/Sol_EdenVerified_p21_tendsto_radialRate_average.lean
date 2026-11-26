-- Prove2me | solution 1 for EdenVerified.p21_tendsto_radialRate_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:30:19.299055+00:00
-- url     : https://prove2.me/submissions/c64abe35-493e-4f4c-92b4-1d1299cccf64

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_radialRate_average


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
      radialRate (squaredRadiusEvolution τ s)) / t) atTop
      (𝓝 (radialRate (limitingSquaredRadius s))) :=
  @Eden.tendsto_radialRate_average
end EdenVerified
