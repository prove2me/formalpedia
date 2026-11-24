-- Prove2me | solution 1 for Formalism.HC.Der.Rd.log_discr_tower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:19.935136+00:00
-- url     : https://prove2.me/submissions/6ac6d744-21a0-4f6e-b19e-8c999fcf7c58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Theorems.Thm_Formalism_HC_Der_Rd_gal_inj
import Theorems.Thm_Formalism_HC_Der_Rd_absNorm_diff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Polynomial ArithmeticFunction
noncomputable section
namespace Formalism.HC.Der.Rd
private theorem absNorm_map_algebraMap_eq_pow_finrank {L E : Type*} [Field L] [NumberField L] [Field E] [NumberField E]
    [Algebra E L] (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 E) (𝓞 L))) = Ideal.absNorm I ^ Module.finrank E L := by
  have hr : Module.finrank (𝓞 E) (𝓞 L) = Module.finrank E L := by
    exact (IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L).symm
  rw [Ideal.absNorm_algebraMap (𝓞 E) (𝓞 L) I, hr]
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open NumberField IntermediateField Polynomial ArithmeticFunction
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ
open Classical
namespace Formalism.HC.Der.Rd
theorem _root_.solution : Real.log |(discr L : ℝ)| =
    ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| +
      Module.finrank E L * Real.log |(discr E : ℝ)| := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  have hD := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 L)
  have h1 : ((Ideal.absNorm (differentIdeal ℤ (𝓞 L)) : ℕ) : ℝ) = |(discr L : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal L (𝓞 L)]
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hE : ((Ideal.absNorm (differentIdeal ℤ (𝓞 E)) : ℕ) : ℝ) = |(discr E : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal E (𝓞 E)]
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hne : ∀ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1,
      |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| ≠ 0 := by
    intro σ hσ
    have hσ1 : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    have hne : ζ - σ ζ ≠ 0 := by
      intro h
      apply hσ1
      apply gal_inj hζ E
      exact (sub_eq_zero.1 h).symm
    rw [abs_ne_zero, Rat.cast_ne_zero]
    exact Algebra.norm_ne_zero_iff.2 hne
  have hdE : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  rw [← h1, hD, map_mul, absNorm_map_algebraMap_eq_pow_finrank, Nat.cast_mul, Nat.cast_pow, absNorm_diff hζ E,
    hE, Real.log_mul (Finset.prod_ne_zero_iff.2 hne) (pow_ne_zero _ hdE), Real.log_prod hne, Real.log_pow]
end Formalism.HC.Der.Rd
