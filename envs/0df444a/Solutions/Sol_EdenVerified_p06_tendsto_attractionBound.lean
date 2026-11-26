-- Prove2me | solution 1 for EdenVerified.p06_tendsto_attractionBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:11.556186+00:00
-- url     : https://prove2.me/submissions/f64cdc13-bcf4-42d3-a8a4-d6780c0844cd

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_attractionBound


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c M : ℝ} (hc : 0 < c) (hM : Real.sqrt 2 < M) (W : ℝ),
    Tendsto (fun t => attractionBound c M W t) atTop (𝓝 0) :=
  @Eden.tendsto_attractionBound
end EdenVerified
