-- Prove2me | solution 1 for Formalism.MainNotions.Pf14.dvd_of_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:11.52841+00:00
-- url     : https://prove2.me/submissions/56ae715f-91cf-43f4-a8fb-d92b832311cd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ScaleEdges_DvdOfAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Pf14
open Module
namespace Formalism.MainNotions.Pf14
theorem _root_.solution {O : Type*} [CommRing O] [IsLocalRing O] (π : O) (hπ : ¬ IsUnit π) (D : ℕ) (a z : O)
    (ha : a ∣ π ^ D) : (a + π ^ (D + 1) * z) ∣ π ^ D := by
  obtain ⟨c, hc⟩ := ha
  have hu : IsUnit (1 + π * c * z) := by
    by_contra h1
    have hm : π * c * z ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hπ))
    have h2 : 1 + π * c * z ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h1
    have h3 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      simpa using Ideal.sub_mem _ h2 hm
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hx : a + π ^ (D + 1) * z = a * (1 + π * c * z) := by
    rw [pow_succ, hc]; ring
  rw [hx, hu.mul_right_dvd]
  exact ⟨c, hc⟩
end Formalism.MainNotions.Pf14
