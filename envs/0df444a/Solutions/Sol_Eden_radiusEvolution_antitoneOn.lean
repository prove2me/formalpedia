-- Prove2me | solution 1 for Eden.radiusEvolution_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:15.72174+00:00
-- url     : https://prove2.me/submissions/4bd1bc6a-bc8a-46a4-b370-828853be7841

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
import Theorems.Thm_Eden_radiusEvolution_nonneg
import Theorems.Thm_Eden_radiusEvolution_ge_sqrt_two
import Theorems.Thm_Eden_hasDerivAt_radiusEvolution

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {R : ℝ} (hR : Real.sqrt 2 ≤ R) :
    AntitoneOn (fun t => radiusEvolution t R) (Ici 0) := by
  have hR₀ : 0 ≤ R := (Real.sqrt_nonneg _).trans hR
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun t ht => (hasDerivAt_radiusEvolution ht hR₀).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_radiusEvolution (interior_subset ht) hR₀).hasDerivWithinAt)
  intro t ht
  have hRt := radiusEvolution_ge_sqrt_two (interior_subset ht) hR
  have hRn := radiusEvolution_nonneg t R
  have hsq : 2 ≤ radiusEvolution t R ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  unfold radialField
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hRn) (by linarith)) (by linarith)
end Eden
