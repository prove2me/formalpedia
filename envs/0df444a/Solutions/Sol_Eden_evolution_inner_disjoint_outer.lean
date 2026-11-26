-- Prove2me | solution 1 for Eden.evolution_inner_disjoint_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:28.656333+00:00
-- url     : https://prove2.me/submissions/c1b1e91b-65fe-4dfc-b890-6d9175aa4589

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
import Theorems.Thm_Eden_radialRegions_disjoint
import Theorems.Thm_Eden_evolution_image_innerRadialRegion

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Disjoint (evolution c t '' innerRadialRegion) outerRadialRegion := by
  rw [evolution_image_innerRadialRegion c ht]
  exact radialRegions_disjoint
end Eden
