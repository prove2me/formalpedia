-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:51.774256+00:00
-- url     : https://prove2.me/submissions/0c1a386b-d216-46d9-b91d-44274dd14757

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
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
    (I J : Ideal S) :
    derivIdeal k (I * J) ≤ I * derivIdeal k J ⊔ J * derivIdeal k I := by
  rw [derivIdeal_le_iff]
  constructor
  · rw [Ideal.mul_le]
    intro r hr s hs
    exact Submodule.mem_sup_left (Ideal.mul_mem_mul hr (le_derivIdeal k J hs))
  · intro D x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      simp only [Derivation.leibniz, smul_eq_mul]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.mem_sup_left
          (Ideal.mul_mem_mul hm (derivation_apply_mem_derivIdeal k J D hn))
      · exact Submodule.mem_sup_right
          (Ideal.mul_mem_mul hn (derivation_apply_mem_derivIdeal k I D hm))
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
end FunctorialResolution.EmbeddedResolution
