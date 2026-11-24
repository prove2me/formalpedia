-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.different_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:06:02.329168+00:00
-- url     : https://prove2.me/submissions/c246b59a-19eb-41c2-9057-7e7595fd0831

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_eq_of_le_of_absNorm_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HF_Final_quadDiscr
import Theorems.Thm_Formalism_HF_P_quad_not_sq_rat
import Theorems.Thm_Formalism_HF_quadDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
namespace Formalism.MainNotions.UnusedSlot33.HK
theorem _root_.solution (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a)
    (h4 : a % 4 = 1) (h1 : a ≠ 1) (x' : 𝓞 K) (hx' : (x' : K) = x) :
    differentIdeal ℤ (𝓞 K) = Ideal.span {x'} := by
  have hdisc : discr K = a := Formalism.HF.quadDiscr K a x hx hadj hsf h4
  have ha0 : a ≠ 0 := hsf.ne_zero
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have hrank : Module.finrank ℚ K = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
    rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
    exact this
  obtain ⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1 := ⟨a / 4, by omega⟩
  have hcK : (a : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω = (1 + x) / 2 := ⟨_, rfl⟩
  have hrelK : ω ^ 2 - ω - (c : K) = 0 := by
    rw [hω]
    linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hcK
  have hωint : IsIntegral ℤ ω := by
    refine ⟨X ^ 2 - X - C c, by monicity!, ?_⟩
    rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast]
    exact hrelK
  obtain ⟨ω', hω'⟩ : ∃ ω' : 𝓞 K, algebraMap (𝓞 K) K ω' = ω := ⟨⟨ω, hωint⟩, rfl⟩
  have hxω : x = 2 * ω - 1 := by rw [hω]; ring
  have hadjω : IntermediateField.adjoin ℚ {ω} = ⊤ := by
    rw [eq_top_iff, ← hadj, IntermediateField.adjoin_simple_le_iff, hxω]
    have hm := IntermediateField.mem_adjoin_simple_self ℚ ω
    exact sub_mem (mul_mem (ofNat_mem _ 2) hm) (one_mem _)
  have hdeg : (minpoly ℚ ω).natDegree = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := ω) (.of_finite ℚ ω)
    rw [hadjω, IntermediateField.finrank_top', hrank] at this
    exact this.symm
  have hint' : IsIntegral ℤ ω' := RingOfIntegers.isIntegral ω'
  have hdegZ : (minpoly ℤ ω').natDegree = 2 := by
    have hmap := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hint'
    rw [hω'] at hmap
    rw [← (minpoly.monic hint').natDegree_map (algebraMap ℤ ℚ), ← hmap]
    exact hdeg
  have hPmon : (X ^ 2 - X - C c : ℤ[X]).Monic := by monicity!
  have hPdeg : (X ^ 2 - X - C c : ℤ[X]).natDegree = 2 := by compute_degree!
  have hrel : ω' ^ 2 - ω' - (c : 𝓞 K) = 0 := by
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, map_intCast, map_zero, hω']
    exact hrelK
  have hP : (X ^ 2 - X - C c : ℤ[X]) = minpoly ℤ ω' := by
    refine minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly hPmon ?_ ?_
    · simpa using hrel
    · rw [degree_eq_natDegree hPmon.ne_zero, degree_eq_natDegree (minpoly.ne_zero hint'), hPdeg,
        hdegZ]
  have hAdj : Algebra.adjoin ℚ {algebraMap (𝓞 K) K ω'} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := ℚ) (α := ω)
      (Algebra.IsAlgebraic.isAlgebraic ω)
    rw [hadjω, IntermediateField.top_toSubalgebra] at this
    rw [hω']
    exact this.symm
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K ω' hAdj
  rw [← hP] at hmem
  have hder : derivative (X ^ 2 - X - C c : ℤ[X]) = C 2 * X - 1 := by
    rw [derivative_sub, derivative_sub, derivative_X_pow, derivative_X, derivative_C, sub_zero]
    norm_num
  have hx'' : x' = 2 * ω' - 1 := by
    apply RingOfIntegers.coe_injective
    show algebraMap (𝓞 K) K x' = algebraMap (𝓞 K) K (2 * ω' - 1)
    rw [map_sub, map_mul, map_one, hω', map_ofNat]
    exact hx'.trans hxω
  have hval : aeval ω' (derivative (X ^ 2 - X - C c : ℤ[X])) = x' := by
    rw [hder, hx'', map_sub, map_mul, aeval_C, aeval_X, map_one]
    simp
  rw [hval] at hmem
  have hle : Ideal.span {x'} ≤ differentIdeal ℤ (𝓞 K) :=
    (Ideal.span_singleton_le_iff_mem _).2 hmem
  have hn : (Algebra.norm ℤ x') ^ 2 = a ^ 2 := by
    have : ((Algebra.norm ℤ x' : ℤ) : ℚ) ^ 2 = (a : ℚ) ^ 2 := by
      rw [Algebra.coe_norm_int, hx', ← map_pow, hx, show ((a : ℤ) : K) = algebraMap ℚ K a by simp,
        Algebra.norm_algebraMap, hrank]
    exact_mod_cast this
  have hN1 : Ideal.absNorm (Ideal.span {x'}) = a.natAbs := by
    rw [Ideal.absNorm_span_singleton]
    exact Int.natAbs_eq_iff_sq_eq.2 hn
  have hN2 : Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = a.natAbs := by
    rw [NumberField.absNorm_differentIdeal K (𝓞 K), hdisc]
  exact (eq_of_le_of_absNorm_eq hle (by rw [hN1]; exact Int.natAbs_ne_zero.2 ha0)
    (hN1.trans hN2.symm)).symm
end Formalism.MainNotions.UnusedSlot33.HK
