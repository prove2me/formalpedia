-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.real_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:29.976468+00:00
-- url     : https://prove2.me/submissions/be80d4b4-92bd-4810-bb14-943ab4d0da4a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_conj_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Discr
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (ψ : K →+* ℂ) : starRingEnd ℂ (ψ (ζ + ζ⁻¹)) = ψ (ζ + ζ⁻¹) := by
  have hw : (ψ ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hc := conj_root hm hw
  simp only [map_add, map_inv₀, hc, inv_inv, add_comm]
end Formalism.FrobeniusOrbits.Discr
