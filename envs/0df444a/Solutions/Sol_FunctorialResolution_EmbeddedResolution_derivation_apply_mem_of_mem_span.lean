-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivation_apply_mem_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:45.36144+00:00
-- url     : https://prove2.me/submissions/4e251355-fe6b-4ffe-9f6d-d2f25c5314cd

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal

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
theorem _root_.solution {k : Type*} [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (D : Derivation k S S) {G : Set S} {T : Ideal S} (hGT : Ideal.span G ≤ T)
    (hD : ∀ g ∈ G, D g ∈ T) {x : S} (hx : x ∈ Ideal.span G) : D x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem g hg => exact hD g hg
  | zero => simp
  | add a b _ _ iha ihb => simpa using Submodule.add_mem T iha ihb
  | smul a b hb ihb =>
      have hb' : b ∈ T := hGT hb
      have hD' : D (a • b) = a • D b + b • D a := by
        rw [smul_eq_mul, D.leibniz]
      rw [hD', smul_eq_mul, smul_eq_mul]
      exact Submodule.add_mem T (Ideal.mul_mem_left T a ihb) (Ideal.mul_mem_right (D a) T hb')
end FunctorialResolution.EmbeddedResolution
