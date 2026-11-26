-- Prove2me | solution 1 for Eden.evolution_image_innerRadialRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:45.004942+00:00
-- url     : https://prove2.me/submissions/b7c813d5-a4e2-4759-8586-88bd267aac4a

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
import Theorems.Thm_P2M_Eden_radiusSq__evolution_lt_one_iff_5cac5d742e9b
import Theorems.Thm_Eden_evolution_mem_attractor
import Theorems.Thm_Eden_evolution_surjOn_attractor

section
noncomputable section
open Set
namespace Eden
private theorem evolution_image_radialRegion (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (P : PhaseSpace → Prop) (hP : ∀ p, P (evolution c t p) ↔ P p) :
    evolution c t '' {p | p ∈ attractor ∧ P p} = {p | p ∈ attractor ∧ P p} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨evolution_mem_attractor c ht hp.1, (hP p).mpr hp.2⟩
  · intro hq
    obtain ⟨p, hp, he⟩ := evolution_surjOn_attractor c ht hq.1
    refine ⟨p, ⟨hp, ?_⟩, he⟩
    exact (hP p).mp (he ▸ hq.2)
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' innerRadialRegion = innerRadialRegion :=
  evolution_image_radialRegion c ht _ (radiusSq₁_evolution_lt_one_iff c ht)
end Eden
