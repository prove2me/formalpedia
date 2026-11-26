-- Prove2me | solution 1 for Eden.isBounded_evolution_image_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:39.910838+00:00
-- url     : https://prove2.me/submissions/3924b4d5-9eec-456e-a3df-2622d6906bd5

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative
import Theorems.Thm_Eden_continuousOn_evolution


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c T : ℝ) (p : PhaseSpace) :
    Bornology.IsBounded ((fun t => evolution c t p) '' Icc 0 T) :=
  (isCompact_Icc.image_of_continuousOn
    ((continuousOn_evolution c p).mono Icc_subset_Ici_self)).isBounded
end Eden
