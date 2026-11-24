-- Prove2me | solution 1 for Formalism.HC.Der.unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:15.960555+00:00
-- url     : https://prove2.me/submissions/621a734c-b91a-421c-b991-db3bcf4ed800

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_HC_Der_kc_smul_ne_bot
import Theorems.Thm_Formalism_HC_Der_kc_mem_inv_smul
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.HC.Der
theorem _root_.solution : ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → ∀ x : H.E,
    x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
      ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
        Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range := by
  intro B hdiff x
  have hD0 := differentIdeal_ne_bot (A := 𝓞 H.K) (B := 𝓞 H.E)
  have hB : B ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_mul] at hdiff
    exact hD0 hdiff
  have hJ : ((H.conj • B : Ideal (𝓞 H.E)) :
      FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H H.conj B hB)
  have hdual : FractionalIdeal.dual (𝓞 H.K) H.K
      (((H.conj • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) =
      ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by
    rw [FractionalIdeal.dual_eq_mul_inv, inv_inv,
      ← inv_inv (FractionalIdeal.dual (𝓞 H.K) H.K
        (1 : FractionalIdeal (𝓞 H.E)⁰ H.E)),
      ← coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E),
      hdiff, FractionalIdeal.coeIdeal_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hJ, mul_one]
  have hx : x ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ ↔
      x ∈ FractionalIdeal.dual (𝓞 H.K) H.K
        (((H.conj • B : Ideal (𝓞 H.E)) :
          FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) := by
    rw [hdual]
  rw [hx, FractionalIdeal.mem_dual (inv_ne_zero hJ)]
  constructor
  · intro hh y hy
    have := hh (H.conj y) ((kc_mem_inv_smul H H.conj B hB y).mpr hy)
    rwa [Algebra.traceForm_apply] at this
  · intro hh z hz
    rw [Algebra.traceForm_apply]
    have hz' : H.conj (H.conj.symm z) = z := H.conj.apply_symm_apply z
    rw [← hz'] at hz ⊢
    exact hh _ ((kc_mem_inv_smul H H.conj B hB _).mp hz)
end Formalism.HC.Der
