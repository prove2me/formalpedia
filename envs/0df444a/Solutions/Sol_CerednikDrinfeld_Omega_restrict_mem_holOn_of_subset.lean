-- Prove2me | solution 1 for CerednikDrinfeld.Omega.restrict_mem_holOn_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7298dfcb-fb3d-52e7-9462-2e24d3c11214

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S T : Set K} (hTS : T ⊆ S) {f : ↥S → K} (hf : f ∈ holOn K S) :
    (fun z : ↥T => f ⟨(z : K), hTS z.2⟩) ∈ holOn K T := by
  rw [mem_holOn_iff] at hf ⊢
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  exact ⟨r, fun k z hz => hr k z (hTS hz), ⟨b, fun k z => hb k ⟨(z : K), hTS z.2⟩⟩,
    hlim.comp (fun z : ↥T => (⟨(z : K), hTS z.2⟩ : ↥S))⟩

end S_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset (solution)
