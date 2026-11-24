-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeylModuleIntRat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:08.655362+00:00
-- url     : https://prove2.me/submissions/09dc3e52-eae3-4f65-804f-380e6c7d556a

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylIntRat
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_map_colAddGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_mem_dualWeyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
private theorem isWeightedHomogeneous_of_map_of_injective {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) {σ M : Type*} [AddCommMonoid M] {w : σ → M}
    {m : M} {f : MvPolynomial σ R} (hf : IsWeightedHomogeneous w (map φ f) m) :
    IsWeightedHomogeneous w f m := by
  intro d hd
  apply hf
  rw [MvPolynomial.coeff_map]
  intro h0
  exact hd (hφ (h0.trans (map_zero φ).symm))
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : DualWeylIntRat := by
  intro r n ν f
  have hφ : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  constructor
  · exact dualWeylModuleMap ℤ ℚ (Int.castRingHom ℚ) r n ν f
  · intro h
    rw [lsat_mem_dualWeyl] at h ⊢
    obtain ⟨hw, hc⟩ := h
    refine ⟨isWeightedHomogeneous_of_map_of_injective hφ hw, ?_⟩
    intro l j hlj
    apply MvPolynomial.map_injective (f := Int.castRingHom ℚ) hφ
    rw [lsat_map_colAddGen, MvPolynomial.map_rename]
    exact hc l j hlj
end Formalism.GradedWeylDivisibility
