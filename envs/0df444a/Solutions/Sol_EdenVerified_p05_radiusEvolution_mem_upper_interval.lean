-- Prove2me | solution 1 for EdenVerified.p05_radiusEvolution_mem_upper_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:16.532428+00:00
-- url     : https://prove2.me/submissions/062fc978-490d-40c6-a8a1-d3c73b513048

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_mem_upper_interval


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (t : ℝ) {r : ℝ}
    (hr₁ : 1 ≤ r) (hr₂ : r ≤ Real.sqrt 2),
    radiusEvolution t r ∈ Set.Icc 1 (Real.sqrt 2) :=
  @Eden.radiusEvolution_mem_upper_interval
end EdenVerified
