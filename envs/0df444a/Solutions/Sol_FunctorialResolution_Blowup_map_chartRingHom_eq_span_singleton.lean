-- Prove2me | solution 1 for FunctorialResolution.Blowup.map_chartRingHom_eq_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:16:27.080032+00:00
-- url     : https://prove2.me/submissions/b04f06c1-3d67-4ca0-9188-c4e4b53a3705

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_coe_eq_chartFraction_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (a : ↥I) :
    Ideal.map (chartRingHom I a) I = Ideal.span {chartRingHom I a (a : R)} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨chartFraction I a ⟨x, hx⟩, (chartRingHom_coe_eq_chartFraction_mul I a ⟨x, hx⟩).symm⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ a.2
end FunctorialResolution.Blowup
