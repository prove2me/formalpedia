-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.le_ramificationIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:06.48532+00:00
-- url     : https://prove2.me/submissions/fb988b7d-c0ce-4b9b-bd77-acb383f70548

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_intCast_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L] (k : ℕ) (ζ : L)
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    2 ^ k ≤ P.ramificationIdx ℤ := by
  set Z : 𝓞 L := ⟨ζ, hζ.isIntegral (by positivity)⟩ with hZdef
  have hZ : IsPrimitiveRoot Z (2 ^ (k + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
  have hassoc : Associated ((Z - 1) ^ (2 ^ k)) (2 : 𝓞 L) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : (Polynomial.cyclotomic (2 ^ (k + 1)) (𝓞 L)).eval 1 = 2 := by
      simp [Polynomial.eval_one_cyclotomic_prime_pow (R := 𝓞 L) (p := 2) k]
    rw [← h2, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hZ, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have htot : (2 : ℕ) ^ k = (2 ^ (k + 1)).totient := by
      rw [Nat.totient_prime_pow_succ Nat.prime_two]
      simp
    rw [htot, ← hZ.card_primitiveRoots, ← Finset.prod_const]
    refine Associated.prod _ _ _ fun η hη => ?_
    obtain ⟨i, -, hi, rfl⟩ := hZ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
    simpa using (hZ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right
  have h2P : (2 : 𝓞 L) ∈ P := by
    have := (two_intCast_mem_iff P 2).mpr dvd_rfl
    simpa using this
  have hZP : Z - 1 ∈ P := by
    obtain ⟨u, hu⟩ := hassoc
    have : (Z - 1) ^ (2 ^ k) = 2 * ↑u⁻¹ := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    exact hP.mem_of_pow_mem _ (this ▸ P.mul_mem_right _ h2P)
  have hmap : map (algebraMap ℤ (𝓞 L)) (span {(2 : ℤ)}) = span {(2 : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hle : span {(2 : 𝓞 L)} ≤ P ^ (2 ^ k) := by
    rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc, ← Ideal.span_singleton_pow]
    exact pow_le_pow_left' ((Ideal.span_singleton_le_iff_mem P).mpr hZP) _
  have hne : map (algebraMap ℤ (𝓞 L)) (span {(2 : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  rw [IsDedekindDomain.ramificationIdx_eq_multiplicity (span {(2 : ℤ)}) P hne]
  apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
  · exact FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hP.ne_top) hne
  · rw [Ideal.dvd_iff_le, hmap]
    exact hle
end Formalism.TwoAdicCyclotomicDecomposition
