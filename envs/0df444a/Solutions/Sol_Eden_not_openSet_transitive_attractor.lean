-- Prove2me | solution 1 for Eden.not_openSet_transitive_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:51.977156+00:00
-- url     : https://prove2.me/submissions/91acaac7-9565-424a-85e9-65381534b49b

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
import Theorems.Thm_Eden_innerRadialRegion_nonempty
import Theorems.Thm_Eden_outerRadialRegion_nonempty
import Theorems.Thm_Eden_isOpen_innerRadialRegion
import Theorems.Thm_Eden_isOpen_outerRadialRegion
import Theorems.Thm_P2M_Eden_one_lt_radiusSq__evolution_iff_356d16ba0e6d

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) :
    ¬ (∀ U V : Set attractor, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ (t : ℝ) (ht : 0 ≤ t) (p : attractor), p ∈ U ∧ attractorEvolution c ht p ∈ V) := by
  intro htrans
  obtain ⟨p, hp⟩ := innerRadialRegion_nonempty
  obtain ⟨q, hq⟩ := outerRadialRegion_nonempty
  obtain ⟨t, ht, r, hr, hs⟩ := htrans
    {p : attractor | (p : PhaseSpace) ∈ innerRadialRegion}
    {p : attractor | (p : PhaseSpace) ∈ outerRadialRegion}
    isOpen_innerRadialRegion isOpen_outerRadialRegion
    ⟨⟨p, hp.1⟩, hp⟩ ⟨⟨q, hq.1⟩, hq⟩
  have hlt : radiusSq₁ r.val < 1 := hr.2
  have hgt : 1 < radiusSq₁ (evolution c t r.val) := hs.2
  exact (not_lt_of_ge hlt.le) ((one_lt_radiusSq₁_evolution_iff c ht r.val).mp hgt)
end Eden
