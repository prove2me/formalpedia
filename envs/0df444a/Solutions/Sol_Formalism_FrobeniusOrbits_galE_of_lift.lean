-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.galE_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:13.997066+00:00
-- url     : https://prove2.me/submissions/c7c93e36-c0a7-4bd1-bcb2-b63d96b6c6fe

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_hcl_eq_hcl_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
section
open NumberField IntermediateField
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
section Hcl
variable {e : ℕ}
end Hcl
section Subfields
variable {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}
end Subfields
section Signs
variable {e : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}
end Signs
section Layer
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
private lemma hcl_eq_of_pow_add_inv_pow_eq {M : Type} [Field M] {e : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2)))
    (u v : (ZMod (2 ^ (e + 2)))ˣ)
    (huv : ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val =
      ζ ^ (v : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (v : ZMod (2 ^ (e + 2))).val) :
    hcl e u = hcl e v := by
  rw [hcl_eq_hcl_iff]
  have hz : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ two_ne_zero)
  have hx2 : ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have hy2 : ζ ^ (v : ZMod (2 ^ (e + 2))).val * ζ⁻¹ ^ (v : ZMod (2 ^ (e + 2))).val = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have key : (ζ ^ (u : ZMod (2 ^ (e + 2))).val - ζ ^ (v : ZMod (2 ^ (e + 2))).val) *
      (ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ ^ (v : ZMod (2 ^ (e + 2))).val - 1) = 0 := by
    linear_combination (ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ ^ (v : ZMod (2 ^ (e + 2))).val) * huv -
      ζ ^ (v : ZMod (2 ^ (e + 2))).val * hx2 + ζ ^ (u : ZMod (2 ^ (e + 2))).val * hy2
  rcases mul_eq_zero.1 key with h1 | h1
  · left
    have h3 := sub_eq_zero.1 h1
    have hij := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3
    exact Units.ext (ZMod.val_injective _ hij)
  · right
    have h3 : ζ ^ ((u : ZMod (2 ^ (e + 2))).val + (v : ZMod (2 ^ (e + 2))).val) = 1 := by
      rw [pow_add]
      exact sub_eq_zero.1 h1
    have h4 := (hζ.pow_eq_one_iff_dvd _).1 h3
    have h5 := (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).2 h4
    push_cast at h5
    simp only [ZMod.natCast_val, ZMod.cast_id', id] at h5
    apply Units.ext
    rw [Units.val_neg]
    exact eq_neg_of_add_eq_zero_left h5
end Layer
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (h : IsLayer (e + 2) q d ζ a b) {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b}
    {τ : L ≃ₐ[ℚ] L} (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) :
    galE e ζ a b σ =
      (((galMap h.1 a b τ).2.1, (galMap h.1 a b τ).2.2), hcl e (galMap h.1 a b τ).1) := by
  have hs : ∀ (x : hostE ζ a b) (y : L), (x : L) = y → Formalism.TwoAdicCyclotomicDecomposition.sgn σ x = Formalism.TwoAdicCyclotomicDecomposition.sgn τ y := by
    intro x y hxy
    have hiff : σ x = x ↔ τ y = y := by
      rw [Subtype.ext_iff, hστ, hxy]
    unfold Formalism.TwoAdicCyclotomicDecomposition.sgn
    by_cases h1 : σ x = x
    · rw [if_pos h1, if_pos (hiff.1 h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.2 h2))]
  have hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val +
        ζ⁻¹ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val := by
    rw [hστ]
    show τ (ζ + ζ⁻¹) = _
    rw [map_add, map_inv₀, ← h.1.autToPow_spec ℚ τ, inv_pow]
  unfold galE galMap
  dsimp only
  rw [hs (aE ζ a b) a rfl, hs (bE ζ a b) b rfl]
  congr 1
  unfold hPart
  have hex : ∃ u : (ZMod (2 ^ (e + 2)))ˣ, ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val := ⟨_, hθ⟩
  rw [dif_pos hex]
  exact hcl_eq_of_pow_add_inv_pow_eq h.1 _ _ ((Classical.choose_spec hex).symm.trans hθ)
end Formalism.FrobeniusOrbits
