-- Prove2me | solution 1 for EdenVerified.s08_radial_regions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:30.888554+00:00
-- url     : https://prove2.me/submissions/95777b96-ebef-4c15-a6df-27857441f85d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_evolution_image_innerRadialRegion
import Theorems.Thm_Eden_evolution_image_outerRadialRegion
import Theorems.Thm_Eden_evolution_image_unitRadialLevel
import Theorems.Thm_Eden_innerRadialRegion_nonempty
import Theorems.Thm_Eden_isOpen_innerRadialRegion
import Theorems.Thm_Eden_isOpen_outerRadialRegion
import Theorems.Thm_Eden_outerRadialRegion_nonempty
import Theorems.Thm_Eden_radialRegions_disjoint


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) :
    innerRadialRegion.Nonempty ∧ outerRadialRegion.Nonempty ∧
    Disjoint innerRadialRegion outerRadialRegion ∧
    IsOpen {p : attractor | (p : PhaseSpace) ∈ innerRadialRegion} ∧
    IsOpen {p : attractor | (p : PhaseSpace) ∈ outerRadialRegion} ∧
    (∀ t : ℝ, 0 ≤ t → evolution c t '' innerRadialRegion = innerRadialRegion ∧
      evolution c t '' outerRadialRegion = outerRadialRegion ∧
      evolution c t '' unitRadialLevel = unitRadialLevel) :=
  ⟨innerRadialRegion_nonempty, outerRadialRegion_nonempty, radialRegions_disjoint,
    isOpen_innerRadialRegion, isOpen_outerRadialRegion,
    fun t ht => ⟨evolution_image_innerRadialRegion c ht,
      evolution_image_outerRadialRegion c ht, evolution_image_unitRadialLevel c ht⟩⟩
end EdenVerified
