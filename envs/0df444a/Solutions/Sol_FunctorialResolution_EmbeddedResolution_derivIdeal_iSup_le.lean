-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_iSup_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:25.193239+00:00
-- url     : https://prove2.me/submissions/63e921ba-ccbf-4cad-ab88-cabdfcbbea6a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_of_mem_span
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {ι : Sort*} (J : ι → Ideal S) :
    derivIdeal k (⨆ i, J i) ≤ ⨆ i, derivIdeal k (J i) := by
  have hspan : (⨆ i, J i) = Ideal.span (⋃ i, (J i : Set S)) := Submodule.iSup_eq_span J
  have hle : (⨆ i, J i) ≤ ⨆ i, derivIdeal k (J i) :=
    iSup_le fun i => (le_derivIdeal k (J i)).trans (le_iSup (fun j => derivIdeal k (J j)) i)
  rw [derivIdeal_le_iff]
  refine ⟨hle, ?_⟩
  intro D x hx
  rw [hspan] at hx
  refine derivation_apply_mem_of_mem_span D ?_ ?_ hx
  · rw [← hspan]
    exact hle
  · intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    have hi' : g ∈ J i := hi
    exact le_iSup (fun j => derivIdeal k (J j)) i
      (derivation_apply_mem_derivIdeal k (J i) D hi')
end FunctorialResolution.EmbeddedResolution
