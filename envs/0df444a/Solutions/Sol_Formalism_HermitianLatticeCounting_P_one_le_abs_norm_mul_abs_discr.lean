-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.one_le_abs_norm_mul_abs_discr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:46.701028+00:00
-- url     : https://prove2.me/submissions/b63a9fdb-3570-4af1-bfb1-1c0b4981905d

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open NumberField
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {E : Type} [Field E] [NumberField E] (z : E) (hz : z ≠ 0)
    (hint : ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (z * (a : E)) = m) :
    1 ≤ |(Algebra.norm ℚ z : ℚ)| * |(NumberField.discr E : ℚ)| := by
  classical
  have hH : ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (z * (a : E)) = m := by assumption
  have hone : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := one_ne_zero
  have hzD : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual hone]
    intro a ha
    obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = a := by
      first
      | exact (FractionalIdeal.mem_one_iff _).mp ha
      | exact FractionalIdeal.mem_one_iff.mp ha
    subst hb
    obtain ⟨m, hm⟩ := hH b
    refine ⟨m, ?_⟩
    have ht : Algebra.traceForm ℚ E z (algebraMap (𝓞 E) E b) =
        Algebra.trace ℚ E (z * (b : E)) := by
      rw [Algebra.traceForm_apply]
    rw [ht, hm]
    first
    | simp
    | exact eq_intCast _ _
  have hDne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
    intro h
    rw [h] at hzD
    first
    | exact hz ((FractionalIdeal.mem_zero_iff _).mp hzD)
    | exact hz (FractionalIdeal.mem_zero_iff.mp hzD)
    | simp_all
  have hdiff : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
    have hcd := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
    first
    | exact hcd
    | exact hcd.symm
    | simpa using hcd
    | (rw [hcd]; simp)
  have hc0 : ∀ I0 : Ideal (𝓞 E),
      FractionalIdeal.absNorm (I0 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = (Ideal.absNorm I0 : ℚ) := by
    intro I0
    first
    | exact FractionalIdeal.coeIdeal_absNorm I0
    | exact FractionalIdeal.absNorm_coeIdeal I0
    | simp
  have hdn : (Ideal.absNorm (differentIdeal ℤ (𝓞 E)) : ℚ) = |(NumberField.discr E : ℚ)| := by
    first
    | rw [NumberField.absNorm_differentIdeal (K := E)]
    | rw [NumberField.absNorm_differentIdeal E]
    | rw [NumberField.absNorm_differentIdeal (K := E) (𝒪 := 𝓞 E)]
    | rw [NumberField.absNorm_differentIdeal (𝒪 := 𝓞 E)]
    | rw [NumberField.absNorm_differentIdeal E (𝓞 E)]
    first
    | simp
    | (push_cast; rfl)
    | simp [Nat.cast_natAbs, Int.cast_abs]
  obtain ⟨J, hJ⟩ : ∃ J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, J = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) z *
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := ⟨_, rfl⟩
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) z ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hzD
  have hJle : J ≤ 1 := by
    rw [hJ, hdiff]
    calc _ ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) *
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
          first
          | exact mul_le_mul_right' hle _
          | exact mul_le_mul' hle le_rfl
          | exact FractionalIdeal.mul_le_mul_right hle _
          | gcongr
      _ = 1 := mul_inv_cancel₀ hDne
  have hJne : J ≠ 0 := by
    rw [hJ]
    refine mul_ne_zero ?_ ?_
    · intro h
      exact hz (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
    · rw [hdiff]
      exact inv_ne_zero hDne
  obtain ⟨I0, hI0⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJle
  have hI0ne : I0 ≠ ⊥ := by
    rintro rfl
    apply hJne
    rw [← hI0]
    first
    | exact FractionalIdeal.coeIdeal_bot
    | simp
  have hN1 : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI0, hc0]
    have h0 : Ideal.absNorm I0 ≠ 0 := fun h => hI0ne (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have hNJ : FractionalIdeal.absNorm J =
      |(Algebra.norm ℚ z : ℚ)| * |(NumberField.discr E : ℚ)| := by
    rw [hJ, map_mul, FractionalIdeal.absNorm_span_singleton, hc0, hdn]
  rw [← hNJ]
  exact hN1
end Formalism.HermitianLatticeCounting.P
