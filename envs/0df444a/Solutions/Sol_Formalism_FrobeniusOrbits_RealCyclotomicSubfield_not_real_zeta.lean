-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.not_real_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:13:09.776797+00:00
-- url     : https://prove2.me/submissions/817c6313-534b-4d61-a883-d048abf08c25

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
theorem _root_.solution {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) (h2 : ¬ m ∣ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (ψ : K →+* ℂ) : starRingEnd ℂ (ψ ζ) ≠ ψ ζ := by
  intro h
  have h1 : (ψ ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hc := conj_root hm h1
  have hne : ψ ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm] at h1
    exact zero_ne_one h1
  have heq : ψ ζ = (ψ ζ)⁻¹ := h.symm.trans hc
  have hsq : ψ (ζ ^ 2) = ψ 1 := by
    rw [map_pow, map_one, sq]
    calc ψ ζ * ψ ζ = ψ ζ * (ψ ζ)⁻¹ := congrArg (ψ ζ * ·) heq
      _ = 1 := mul_inv_cancel₀ hne
  exact h2 (hζ.dvd_of_pow_eq_one 2 (ψ.injective hsq))
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
