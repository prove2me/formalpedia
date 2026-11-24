-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.maxReal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:41.297706+00:00
-- url     : https://prove2.me/submissions/7768900e-c4b5-4f09-b92b-86dc11f542d8

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_real_theta
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_not_real_zeta
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_real_on_adjoin
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_two_pow_not_dvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Polynomial
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace RealCyclotomicSubfield
variable {L : Type} [Field L] [NumberField L]
private lemma mem_adjoin_of_val_mem_adjoin_image {L' : Type*} [Field L'] [CharZero L'] (Z : IntermediateField ℚ L')
    (S : Set Z) (x : Z) (hx : (x : L') ∈ adjoin ℚ (Z.val '' S)) : x ∈ adjoin ℚ S := by
  rw [← IntermediateField.adjoin_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  exact hy
private lemma finrank_adjoin_add_inv_eq_two_of_isPrimitiveRoot {M : Type*} [Field M] [CharZero M] [FiniteDimensional ℚ M]
    {m : ℕ} (hm : m ≠ 0) (h2 : ¬ m ∣ 2) {z : M} (hz : IsPrimitiveRoot z m) (htop : ℚ⟮z⟯ = ⊤) :
    Module.finrank ℚ⟮z + z⁻¹⟯ M = 2 := by
  have hzK : z ∉ ℚ⟮z + z⁻¹⟯ := by
    intro hz'
    let φ : M →+* ℂ := (IsAlgClosed.lift : M →ₐ[ℚ] ℂ).toRingHom
    exact not_real_zeta hm h2 hz φ (real_on_adjoin _ φ (real_theta hm hz φ) z hz')
  have htop' : adjoin ℚ⟮z + z⁻¹⟯ ({z} : Set M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ ℚ⟮z⟯ := htop ▸ IntermediateField.mem_top
    have key : Subfield.closure (Set.range (algebraMap ℚ M) ∪ {z}) ≤
        (adjoin ℚ⟮z + z⁻¹⟯ ({z} : Set M)).toSubfield := by
      rw [Subfield.closure_le]
      rintro y (⟨q, rfl⟩ | hy)
      · rw [eq_ratCast (algebraMap ℚ M) q]
        exact SubfieldClass.ratCast_mem _ q
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact mem_adjoin_simple_self _ y
    exact key hx
  have hint : IsIntegral ℚ⟮z + z⁻¹⟯ z := IsIntegral.tower_top (Algebra.IsIntegral.isIntegral (R := ℚ) z)
  rw [← IntermediateField.finrank_top', ← htop', IntermediateField.adjoin.finrank hint]
  apply le_antisymm
  · let θK : ℚ⟮z + z⁻¹⟯ := ⟨z + z⁻¹, mem_adjoin_simple_self ℚ _⟩
    have hmon : (X ^ 2 - C θK * X + 1 : (ℚ⟮z + z⁻¹⟯)[X]).Monic := by monicity!
    have hdeg : (X ^ 2 - C θK * X + 1 : (ℚ⟮z + z⁻¹⟯)[X]).natDegree = 2 := by compute_degree!
    have hroot : aeval z (X ^ 2 - C θK * X + 1 : (ℚ⟮z + z⁻¹⟯)[X]) = 0 := by
      have hz0 : z ≠ 0 := hz.ne_zero hm
      simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one]
      show z ^ 2 - (z + z⁻¹) * z + 1 = 0
      rw [add_mul, inv_mul_cancel₀ hz0]
      ring
    rw [← hdeg]
    exact natDegree_le_natDegree (minpoly.min _ z hmon hroot)
  · by_contra hlt
    push_neg at hlt
    have hpos := minpoly.natDegree_pos hint
    have h1 : (minpoly ℚ⟮z + z⁻¹⟯ z).natDegree = 1 := by omega
    obtain ⟨k, hk⟩ := minpoly.natDegree_eq_one_iff.mp h1
    have hk' : (k : M) = z := hk
    exact hzK ((congrArg (fun w => w ∈ ℚ⟮z + z⁻¹⟯) hk').mp k.2)
end RealCyclotomicSubfield
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.RealCyclotomicSubfield
theorem _root_.solution {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    ∀ x : ℚ⟮ζ⟯, x ∈ maximalRealSubfield ℚ⟮ζ⟯ ↔ (x : L) ∈ F1 ζ := by
  intro x
  have hint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional hint
  let z : ℚ⟮ζ⟯ := AdjoinSimple.gen ℚ ζ
  have hz : IsPrimitiveRoot z (2 ^ (e + 2)) :=
    (show IsPrimitiveRoot ((ℚ⟮ζ⟯).val z) (2 ^ (e + 2)) from hζ).of_map_of_injective Subtype.val_injective
  have hm : (2 : ℕ) ^ (e + 2) ≠ 0 := by positivity
  have hK : ∀ y ∈ ℚ⟮z + z⁻¹⟯, y ∈ maximalRealSubfield ℚ⟮ζ⟯ := by
    intro y hy
    rw [NumberField.mem_maximalRealSubfield_iff]
    intro φ
    exact real_on_adjoin _ φ (real_theta hm hz φ) y hy
  have himg : (ℚ⟮ζ⟯).val '' {z + z⁻¹} = {ζ + ζ⁻¹} := by
    rw [Set.image_singleton]
    rfl
  constructor
  · intro hx
    have hxK : x ∈ ℚ⟮z + z⁻¹⟯ := by
      have htop : ℚ⟮z⟯ = ⊤ := by
        rw [eq_top_iff]
        intro w _
        apply mem_adjoin_of_val_mem_adjoin_image
        rw [Set.image_singleton]
        exact w.2
      have h2 := finrank_adjoin_add_inv_eq_two_of_isPrimitiveRoot hm (two_pow_not_dvd e) hz htop
      have hintx : IsIntegral ℚ⟮z + z⁻¹⟯ x :=
        IsIntegral.tower_top (Algebra.IsIntegral.isIntegral (R := ℚ) x)
      have hle : (minpoly ℚ⟮z + z⁻¹⟯ x).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le x
      by_contra hxK
      have hne1 : (minpoly ℚ⟮z + z⁻¹⟯ x).natDegree ≠ 1 := by
        intro h1
        obtain ⟨k, hk⟩ := minpoly.natDegree_eq_one_iff.mp h1
        apply hxK
        rw [← hk]
        exact k.2
      have hpos := minpoly.natDegree_pos hintx
      have hdeg2 : (minpoly ℚ⟮z + z⁻¹⟯ x).natDegree = 2 := by omega
      have hA : adjoin ℚ⟮z + z⁻¹⟯ ({x} : Set ℚ⟮ζ⟯) = ⊤ :=
        IntermediateField.eq_of_le_of_finrank_eq le_top
          (by rw [IntermediateField.adjoin.finrank hintx, hdeg2, IntermediateField.finrank_top', h2])
      have hsub : (adjoin ℚ⟮z + z⁻¹⟯ ({x} : Set ℚ⟮ζ⟯)).toSubfield ≤ maximalRealSubfield ℚ⟮ζ⟯ := by
        show Subfield.closure (Set.range (algebraMap ℚ⟮z + z⁻¹⟯ ℚ⟮ζ⟯) ∪ {x}) ≤ _
        rw [Subfield.closure_le]
        rintro y (⟨k, rfl⟩ | hy)
        · exact hK _ k.2
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hx
      have hzA : z ∈ adjoin ℚ⟮z + z⁻¹⟯ ({x} : Set ℚ⟮ζ⟯) := by
        rw [hA]
        exact IntermediateField.mem_top
      have hzR : z ∈ maximalRealSubfield ℚ⟮ζ⟯ := hsub hzA
      rw [NumberField.mem_maximalRealSubfield_iff] at hzR
      let φ : ℚ⟮ζ⟯ →+* ℂ := (IsAlgClosed.lift : ℚ⟮ζ⟯ →ₐ[ℚ] ℂ).toRingHom
      exact not_real_zeta hm (two_pow_not_dvd e) hz φ (hzR φ)
    have key : Subfield.closure (Set.range (algebraMap ℚ ℚ⟮ζ⟯) ∪ {z + z⁻¹}) ≤
        (F1 ζ).toSubfield.comap ((ℚ⟮ζ⟯).val : ℚ⟮ζ⟯ →+* L) := by
      rw [Subfield.closure_le]
      rintro y (⟨q, rfl⟩ | hy)
      · show ((ℚ⟮ζ⟯).val : ℚ⟮ζ⟯ →+* L) (algebraMap ℚ ℚ⟮ζ⟯ q) ∈ (F1 ζ).toSubfield
        rw [eq_ratCast (algebraMap ℚ ℚ⟮ζ⟯) q, map_ratCast]
        exact SubfieldClass.ratCast_mem _ q
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        show ζ + ζ⁻¹ ∈ F1 ζ
        exact mem_adjoin_simple_self ℚ _
    exact key hxK
  · intro hx
    apply hK
    apply mem_adjoin_of_val_mem_adjoin_image
    rw [himg]
    exact hx
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
