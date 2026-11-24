-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.absNorm_different
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:27.252974+00:00
-- url     : https://prove2.me/submissions/74214517-f436-41e8-adb5-d03c72da511b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_th_coe
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_minpoly_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_adjoin_top

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
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}
variable [IsCyclotomicExtension {2 ^ (e + 2)} ℚ K]
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    Ideal.absNorm (differentIdeal (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K)) = 4 := by
  have hm : 2 ^ (e + 2) ≠ 0 := by positivity
  have hne : NeZero (2 ^ (e + 2)) := ⟨hm⟩
  have hz0 : z ≠ 0 := hz.ne_zero hm
  have hxz : algebraMap (𝓞 K) K hz.toInteger = z := rfl
  have hadjZ := IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hz
  have hadj : Algebra.adjoin (𝓞 ℚ⟮z + z⁻¹⟯) {hz.toInteger} = ⊤ := by
    rw [eq_top_iff] at hadjZ ⊢
    intro y _
    have hle : Algebra.adjoin ℤ {hz.toInteger} ≤
        (Algebra.adjoin (𝓞 ℚ⟮z + z⁻¹⟯) {hz.toInteger}).restrictScalars ℤ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle (hadjZ Algebra.mem_top)
  have hcond := conductor_mul_differentIdeal (𝓞 ℚ⟮z + z⁻¹⟯) ℚ⟮z + z⁻¹⟯ K hz.toInteger
    (by rw [hxz]; exact adjoin_top hz)
  rw [conductor_eq_top_of_adjoin_eq_top hadj, Ideal.top_mul] at hcond
  rw [hcond, Ideal.absNorm_span_singleton]
  have hint : IsIntegral (𝓞 ℚ⟮z + z⁻¹⟯) z := (hz.isIntegral (Nat.pos_of_ne_zero hm)).tower_top
  have hmin : minpoly ℚ⟮z + z⁻¹⟯ z = Polynomial.map (algebraMap (𝓞 ℚ⟮z + z⁻¹⟯) ℚ⟮z + z⁻¹⟯)
      (minpoly (𝓞 ℚ⟮z + z⁻¹⟯) hz.toInteger) := by
    rw [← minpoly.algebraMap_eq (IsFractionRing.injective (𝓞 K) K) hz.toInteger, hxz]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ⟮z + z⁻¹⟯ hint
  have hw : algebraMap (𝓞 K) K (Polynomial.aeval hz.toInteger
      (Polynomial.derivative (minpoly (𝓞 ℚ⟮z + z⁻¹⟯) hz.toInteger))) = z - z⁻¹ := by
    rw [← Polynomial.aeval_algebraMap_apply, hxz, ← Polynomial.aeval_map_algebraMap ℚ⟮z + z⁻¹⟯,
      ← Polynomial.derivative_map, ← hmin, minpoly_eq hz]
    (try simp [th_coe]) <;> ring
  generalize Polynomial.aeval hz.toInteger
    (Polynomial.derivative (minpoly (𝓞 ℚ⟮z + z⁻¹⟯) hz.toInteger)) = w at hw ⊢
  have hN1 : Algebra.norm ℚ (z - 1) = 2 :=
    hz.norm_sub_one_two (by omega) (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hm))
  have hhalf : z ^ (2 ^ (e + 1)) = -1 := by
    have hsq : z ^ (2 ^ (e + 1)) * z ^ (2 ^ (e + 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hz.pow_eq_one
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h (hz.pow_ne_one_of_pos_of_lt (by positivity)
        (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    · exact h
  have hcop : Nat.Coprime (2 ^ (e + 1) + 1) (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ (Odd.coprime_two_right ⟨2 ^ e, by ring⟩)
  have hneg : IsPrimitiveRoot (-z) (2 ^ (e + 2)) := by
    have h := hz.pow_of_coprime _ hcop
    rwa [pow_succ, hhalf, neg_one_mul] at h
  have hN2 : Algebra.norm ℚ (-z - 1) = 2 :=
    hneg.norm_sub_one_two (by omega) (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hm))
  have hNm1 : |Algebra.norm ℚ (-1 : K)| = 1 := by
    rw [show (-1 : K) = algebraMap ℚ K (-1) by simp, Algebra.norm_algebraMap]
    simp
  have hNz : |Algebra.norm ℚ z| = 1 := by
    have h1 : (Algebra.norm ℚ z) ^ (2 ^ (e + 2)) = 1 := by
      rw [← map_pow, hz.pow_eq_one, map_one]
    have h2 : |Algebra.norm ℚ z| ^ (2 ^ (e + 2)) = 1 := by rw [← abs_pow, h1, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hm).mp h2
  have hprod : z * (z - z⁻¹) = (z - 1) * ((-1) * (-z - 1)) := by
    rw [mul_sub, mul_inv_cancel₀ hz0]
    ring
  have hnorm : |Algebra.norm ℚ (z - z⁻¹)| = 4 := by
    have h := congrArg (fun t => |Algebra.norm ℚ t|) hprod
    simp only [map_mul, abs_mul, hNz, hN1, hN2, hNm1, one_mul] at h
    norm_num at h
    exact h
  have hcast : ((Algebra.norm ℤ w : ℤ) : ℚ) = Algebra.norm ℚ (z - z⁻¹) := by
    rw [← hw]
    exact Algebra.coe_norm_int w
  have habs : |((Algebra.norm ℤ w : ℤ) : ℚ)| = 4 := by rw [hcast]; exact hnorm
  have habsZ : |Algebra.norm ℤ w| = 4 := by exact_mod_cast habs
  rw [Int.abs_eq_natAbs] at habsZ
  exact_mod_cast habsZ
end Formalism.FrobeniusOrbits.Discr
