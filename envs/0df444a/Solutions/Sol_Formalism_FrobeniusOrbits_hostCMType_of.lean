-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostCMType_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:08.309299+00:00
-- url     : https://prove2.me/submissions/1ab39934-3389-4879-b933-5d978f11fed5

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield

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
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hGal : HostGalois) (hSpec : HostGalSpec) : HostCMType := by
  intro e q d hq L _ _ ζ a b h
  obtain ⟨-, hfin, -, -⟩ := hGal e q d hq L ζ a b h
  have hb : b ^ 2 = -(d : L) := h.2.2.1
  have hbE : (bE ζ a b) ^ 2 = -(d : hostE ζ a b) := Subtype.ext (by push_cast; exact hb)
  set c : ℂ := Complex.I * (Real.sqrt d : ℂ) with hcdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hq.2.1.pos
  have hc2 : c ^ 2 = -(d : ℂ) := by
    rw [hcdef, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hd0.le]
    simp
  have hc0 : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hd0).ne')
  have hcc : starRingEnd ℂ c = -c := by
    rw [hcdef, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hcne : c ≠ -c := by
    intro h'
    apply hc0
    have h2c : (2 : ℂ) * c = 0 := by linear_combination h'
    simpa using h2c
  have hroots : ∀ φ : hostE ζ a b →+* ℂ, φ (bE ζ a b) = c ∨ φ (bE ζ a b) = -c := by
    intro φ
    have hsq : (φ (bE ζ a b)) ^ 2 = c ^ 2 := by
      rw [hc2, ← map_pow, hbE, map_neg, map_natCast]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have ha : ∀ φ : hostE ζ a b →+* ℂ,
      φ ∈ cmType ζ a b d ↔ (starRingEnd ℂ).comp φ ∉ cmType ζ a b d := by
    intro φ
    show φ (bE ζ a b) = c ↔ ¬ ((starRingEnd ℂ).comp φ) (bE ζ a b) = c
    rw [RingHom.comp_apply]
    rcases hroots φ with h1 | h1 <;> rw [h1]
    · rw [hcc]
      exact ⟨fun _ => hcne.symm, fun _ => rfl⟩
    · rw [map_neg, hcc, neg_neg]
      exact ⟨fun h' => absurd h' hcne.symm, fun h' => absurd rfl h'⟩
  refine ⟨ha, ?_, ?_⟩
  · haveI : NumberField (hostE ζ a b) := {}
    let f : (hostE ζ a b →+* ℂ) → (hostE ζ a b →+* ℂ) := fun φ => (starRingEnd ℂ).comp φ
    have hinv : Function.Involutive f := fun φ => RingHom.ext fun x => by simp [f]
    have hpre : f ⁻¹' (cmType ζ a b d) = (cmType ζ a b d)ᶜ := by
      ext φ
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      exact ⟨fun h1 h2 => ((ha φ).mp h2) h1, fun h1 => by
        by_contra h2
        exact h1 ((ha φ).mpr h2)⟩
    have himg : f '' (cmType ζ a b d) = (cmType ζ a b d)ᶜ := by
      rw [Set.image_eq_preimage_of_inverse hinv.leftInverse hinv.rightInverse, hpre]
    have hcard := Set.ncard_add_ncard_compl (cmType ζ a b d)
    rw [← himg, Set.ncard_image_of_injective _ hinv.injective, Nat.card_eq_fintype_card,
      NumberField.Embeddings.card, hfin, pow_succ] at hcard
    omega
  · intro φ hφ σ
    have hφ' : φ (bE ζ a b) = c := hφ
    show φ (σ (bE ζ a b)) = c ↔ galE e ζ a b σ ∈ Psi e
    rw [Psi, MonoidHom.mem_ker]
    show _ ↔ sgn σ (bE ζ a b) = 1
    unfold sgn
    by_cases hs : σ (bE ζ a b) = bE ζ a b
    · rw [if_pos hs, hs, hφ']
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    · have hsb : σ (bE ζ a b) = -(bE ζ a b) := by
        have hsq : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2 := by
          rw [← map_pow, hbE, map_neg, map_natCast]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
        · exact absurd h' hs
        · exact h'
      rw [if_neg hs, hsb, map_neg, hφ']
      exact ⟨fun h' => absurd h'.symm hcne, fun h' => absurd h' (by decide)⟩
end Formalism.FrobeniusOrbits
