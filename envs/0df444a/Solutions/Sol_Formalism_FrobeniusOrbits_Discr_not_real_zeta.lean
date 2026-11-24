-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.not_real_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:23.080394+00:00
-- url     : https://prove2.me/submissions/ee63f829-0cb0-440a-a04d-d355596e7cf9

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
theorem _root_.solution {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) (h2 : ¬ m ∣ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (ψ : K →+* ℂ) : starRingEnd ℂ (ψ ζ) ≠ ψ ζ := by
  intro h
  have hp : IsPrimitiveRoot (ψ ζ) m := hζ.map_of_injective ψ.injective
  have hc := conj_root hm hp.pow_eq_one
  have h0 : ψ ζ ≠ 0 := hp.ne_zero hm
  have h1 : ψ ζ = (ψ ζ)⁻¹ := h.symm.trans hc
  have hsq : (ψ ζ) ^ 2 = 1 := by
    rw [sq]
    calc ψ ζ * ψ ζ = ψ ζ * (ψ ζ)⁻¹ := congrArg (HMul.hMul (ψ ζ)) h1
      _ = 1 := mul_inv_cancel₀ h0
  exact h2 (hp.dvd_of_pow_eq_one 2 hsq)
end Formalism.FrobeniusOrbits.Discr
