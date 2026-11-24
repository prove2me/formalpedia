-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.hcl_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:38:40.302977+00:00
-- url     : https://prove2.me/submissions/307ece29-1163-49ce-90dd-aefe4353fa1a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_two_mem_of_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_hcl_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Inertia
theorem _root_.solution (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (τ : Gal(L/ℚ)) (Θ : 𝓞 L)
    (hΘ : (Θ : L) = ζ + ζ⁻¹) (hmem : τ • Θ - Θ ∈ Q) : hcl e (h.1.autToPow ℚ τ) = 1 := by
  have hn : 0 < 2 ^ (e + 2) := by positivity
  have hζ0 : ζ ≠ 0 := h.1.ne_zero hn.ne'
  have h2Q : (2 : 𝓞 L) ∉ Q := by
    intro h2
    have h2' : (2 : ℤ) ∈ Ideal.span {(p : ℤ)} := by
      rw [Ideal.over_def Q (Ideal.span {(p : ℤ)})]
      show algebraMap ℤ (𝓞 L) 2 ∈ Q
      simpa using h2
    rw [Ideal.mem_span_singleton] at h2'
    have hp2' : p ∣ 2 := by exact_mod_cast h2'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')
  set u := h.1.autToPow ℚ τ with hu
  set v := (u : ZMod (2 ^ (e + 2))).val with hv
  have hvlt : v < 2 ^ (e + 2) := ZMod.val_lt _
  have huv : ((v : ℕ) : ZMod (2 ^ (e + 2))) = (u : ZMod (2 ^ (e + 2))) := ZMod.natCast_zmod_val _
  have hτζ : τ ζ = ζ ^ v := (h.1.autToPow_spec ℚ τ).symm
  have hτζi : τ ζ⁻¹ = ζ⁻¹ ^ v := by rw [map_inv₀, hτζ, inv_pow]
  set Z : 𝓞 L := ⟨ζ, h.1.isIntegral hn⟩ with hZ
  set Zi : 𝓞 L := ⟨ζ⁻¹, h.1.inv.isIntegral hn⟩ with hZi
  have eZ : algebraMap (𝓞 L) L Z = ζ := rfl
  have eZi : algebraMap (𝓞 L) L Zi = ζ⁻¹ := rfl
  have hZZi : Z * Zi = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_mul, eZ, eZi, map_one, mul_inv_cancel₀ hζ0]
  have hZn : Z ^ (2 ^ (e + 2)) = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, eZ, map_one]
    exact h.1.pow_eq_one
  have hZin : Zi ^ (2 ^ (e + 2)) = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, eZi, map_one]
    exact h.1.inv.pow_eq_one
  have hdiff : τ • Θ - Θ = Zi ^ v * (Z ^ (v + 1) - 1) * (Z ^ v * Zi - 1) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    have e1 : algebraMap (𝓞 L) L (τ • Θ) = τ ζ + τ ζ⁻¹ := by
      show τ (Θ : L) = _
      rw [hΘ, map_add]
    have e2 : algebraMap (𝓞 L) L Θ = ζ + ζ⁻¹ := hΘ
    simp only [map_sub, map_mul, map_pow, map_one, e1, e2, eZ, eZi, hτζ, hτζi, inv_pow]
    field_simp
    ring
  rw [hdiff] at hmem
  have hQ : Q.IsPrime := inferInstance
  have key : u = 1 ∨ u = -1 := by
    by_contra hne
    push_neg at hne
    apply h2Q
    rcases hQ.mem_or_mem hmem with h12 | h3
    · rcases hQ.mem_or_mem h12 with h1 | h2
      · exfalso
        have h1' := Q.mul_mem_left (Z ^ v) h1
        rw [← mul_pow, hZZi, one_pow] at h1'
        exact hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1')
      · refine two_mem_of_pow Q (e + 2) (Z ^ (v + 1)) ?_ ?_ h2
        · rw [← pow_mul, mul_comm, pow_mul, hZn, one_pow]
        · intro h1
          apply hne.2
          have h1' : ζ ^ (v + 1) = 1 := by
            have := congrArg (algebraMap (𝓞 L) L) h1
            rwa [map_pow, eZ, map_one] at this
          have hdvd := (h.1.pow_eq_one_iff_dvd (v + 1)).1 h1'
          have hv1 : v + 1 = 2 ^ (e + 2) :=
            le_antisymm (by omega) (Nat.le_of_dvd (by omega) hdvd)
          apply Units.ext
          rw [Units.val_neg, Units.val_one, ← huv]
          have h0 : ((v + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 := by
            rw [hv1]; exact ZMod.natCast_self _
          push_cast at h0
          linear_combination h0
    · refine two_mem_of_pow Q (e + 2) (Z ^ v * Zi) ?_ ?_ h3
      · rw [mul_pow, ← pow_mul, mul_comm v, pow_mul, hZn, one_pow, hZin, one_mul]
      · intro h1
        apply hne.1
        have h1' : ζ ^ v = ζ ^ 1 := by
          have := congrArg (algebraMap (𝓞 L) L) h1
          rw [map_mul, map_pow, eZ, eZi, map_one] at this
          rw [pow_one]
          field_simp at this
          exact this
        have hv1 : v = 1 := h.1.pow_inj hvlt (by
          have : 1 < 2 ^ (e + 2) := Nat.one_lt_two_pow (by omega)
          exact this) h1'
        apply Units.ext
        rw [Units.val_one, ← huv, hv1, Nat.cast_one]
  rcases key with h1 | h1
  · rw [h1]
    exact hcl_one e
  · rw [h1]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
end Formalism.FrobeniusOrbits.Inertia
