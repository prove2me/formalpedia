-- Prove2me | solution 1 for CerednikDrinfeld.exists_ringHom_away_comp_eq_and_not_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2009aa11-c9d0-5762-ada8-d09633fcaaec

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff

set_option autoImplicit false

theorem solution
    {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B') (g : B) :
    (∃ fg : Localization.Away g →+* Localization.Away (f g),
        fg.comp (algebraMap B (Localization.Away g)) = (algebraMap B' (Localization.Away (f g))).comp f) ∧
      ∀ x' : PrimeSpectrum B', f g ∉ x'.asIdeal ↔ g ∉ (PrimeSpectrum.comap f x').asIdeal := by
  have hle : Submonoid.powers g ≤ (Submonoid.powers (f g)).comap f := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp [map_pow]⟩
  refine ⟨⟨IsLocalization.map (Localization.Away (f g)) f hle, IsLocalization.map_comp hle⟩, fun x' => ?_⟩
  simp [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]

end S_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff
end P2MW
export P2MW.S_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff (solution)
