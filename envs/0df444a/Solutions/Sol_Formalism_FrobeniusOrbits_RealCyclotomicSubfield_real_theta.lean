-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.real_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:13:11.956603+00:00
-- url     : https://prove2.me/submissions/093d3f07-3097-44a6-bbc3-a789f9afc82c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_conj_root

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
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
namespace Formalism.FrobeniusOrbits.RealCyclotomicSubfield
theorem _root_.solution {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (ψ : K →+* ℂ) : starRingEnd ℂ (ψ (ζ + ζ⁻¹)) = ψ (ζ + ζ⁻¹) := by
  have h1 : (ψ ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hc := conj_root hm h1
  simp only [map_add, map_inv₀]
  rw [hc, inv_inv, add_comm]
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
