-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.galE_snd_eq_hcl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:19.144804+00:00
-- url     : https://prove2.me/submissions/15bd841f-8b13-457a-a847-59ced8e29a98

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_hcl_eq_hcl_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_exists_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_of_lift
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
private lemma zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot {M : Type} [Field M] {e : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2)))
    (x : ZMod (2 ^ (e + 2))) : ζ ^ (-x).val = ζ⁻¹ ^ x.val := by
  have hd : 2 ^ (e + 2) ∣ (-x).val + x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2))]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    exact neg_add_cancel x
  have h1 : ζ ^ ((-x).val + x.val) = 1 := (hζ.pow_eq_one_iff_dvd _).2 hd
  rw [pow_add] at h1
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h1
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
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (u : (ZMod (2 ^ (e + 2)))ˣ) :
    (galE e ζ a b σ).2 = hcl e u ↔
      ((σ (thE ζ a b) : hostE ζ a b) : L) =
        ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val := by
  obtain ⟨τ, hτ⟩ := galE_exists_lift hqd h σ
  have hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val +
        ζ⁻¹ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val := by
    rw [hτ]
    show τ (ζ + ζ⁻¹) = _
    rw [map_add, map_inv₀, ← h.1.autToPow_spec ℚ τ, inv_pow]
  rw [galE_of_lift h hτ]
  unfold galMap
  dsimp only
  rw [hθ]
  constructor
  · intro hk
    rcases (hcl_eq_hcl_iff _ _).1 hk with h1 | h1
    · rw [h1]
    · rw [h1, Units.val_neg, zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot h.1, zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot h.1.inv, inv_inv, add_comm]
  · intro hk
    exact hcl_eq_of_pow_add_inv_pow_eq h.1 _ _ hk
end Formalism.FrobeniusOrbits
