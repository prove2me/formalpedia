-- Prove2me | solution 1 for CohnElkies.uniformAntiFourierSignRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/bf88a87e-2b1a-44e8-a5f5-c2f426f898bc

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_antiFourierWitness_capped_poisson_majorization
import Theorems.Thm_CohnElkies_uniformAntiFourierSignRadius_of_capped_poisson_majorization

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution :
    UniformAntiFourierSignRadius := by
  apply uniformAntiFourierSignRadius_of_capped_poisson_majorization
  intro d hd R hR w
  exact exists_antiFourierWitness_capped_poisson_majorization
    hd hR w
end CohnElkies
