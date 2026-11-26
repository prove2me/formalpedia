-- Prove2me | solution 1 for EdenVerified.p05_radiusEvolution_mem_lower_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:10:49.747578+00:00
-- url     : https://prove2.me/submissions/9b32a239-0652-4c7b-b068-2641ecc988f7

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_mem_lower_interval


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (t : ℝ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1),
    radiusEvolution t r ∈ Set.Icc 0 1 :=
  @Eden.radiusEvolution_mem_lower_interval
end EdenVerified
