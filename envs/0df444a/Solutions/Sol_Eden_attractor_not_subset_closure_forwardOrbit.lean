-- Prove2me | solution 1 for Eden.attractor_not_subset_closure_forwardOrbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:30.788206+00:00
-- url     : https://prove2.me/submissions/8b2bd8e3-9456-42cc-b284-38b4c85d5dd2

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
import Theorems.Thm_Eden_innerRadialRegion_nonempty
import Theorems.Thm_Eden_outerRadialRegion_nonempty
import Theorems.Thm_P2M_Eden_one_lt_radiusSq__evolution_iff_356d16ba0e6d
import Theorems.Thm_P2M_Eden_continuous_radiusSq__4ecf54230f51


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    ¬ attractor ⊆ closure (forwardOrbit c p) := by
  intro hd
  by_cases hp : radiusSq₁ p ≤ 1
  · have hcl : closure (forwardOrbit c p) ⊆ {q | radiusSq₁ q ≤ 1} := by
      apply closure_minimal _ (isClosed_le continuous_radiusSq₁ continuous_const)
      rintro q ⟨t, ht, rfl⟩
      change radiusSq₁ (evolution c t p) ≤ 1
      by_contra h
      exact (not_lt_of_ge hp) ((one_lt_radiusSq₁_evolution_iff c ht p).mp (lt_of_not_ge h))
    obtain ⟨q, hq⟩ := outerRadialRegion_nonempty
    exact (not_lt_of_ge (hcl (hd hq.1))) hq.2
  · have hcl : closure (forwardOrbit c p) ⊆ {q | 1 ≤ radiusSq₁ q} := by
      apply closure_minimal _ (isClosed_le continuous_const continuous_radiusSq₁)
      rintro q ⟨t, ht, rfl⟩
      exact ((one_lt_radiusSq₁_evolution_iff c ht p).mpr (lt_of_not_ge hp)).le
    obtain ⟨q, hq⟩ := innerRadialRegion_nonempty
    exact (not_lt_of_ge (hcl (hd hq.1))) hq.2
end Eden
