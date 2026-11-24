-- Prove2me | solution 1 for Formalism.HC.Der.Rd.log_norm_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:20.063607+00:00
-- url     : https://prove2.me/submissions/57152df5-6e0c-48d1-9298-4dd10cf89367

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
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
private theorem log_abs_eval_one_cyclotomic_eq_vonMangoldt {m : ℕ} (hm : 1 < m) :
    Real.log |((eval 1 (cyclotomic m ℚ) : ℚ) : ℝ)| = vonMangoldt m := by
  by_cases h : IsPrimePow m
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).1 h
    rcases k with _ | j
    · omega
    haveI := Fact.mk hp
    rw [eval_one_cyclotomic_prime_pow, vonMangoldt_apply_pow (Nat.succ_ne_zero j),
      vonMangoldt_apply_prime hp]
    simp
  · rw [eval_one_cyclotomic_not_prime_pow, vonMangoldt_eq_zero_iff.2 h]
    · simp
    · intro p hp k hk
      apply h
      rw [← hk]
      refine hp.isPrimePow.pow ?_
      rintro rfl
      rw [pow_zero] at hk
      omega
private theorem log_abs_norm_sub_one_mul_totient_eq {m : ℕ} (hm : 1 < m) {L : Type*} [Field L] [NumberField L] {η : L}
    (hη : IsPrimitiveRoot η m) :
    Real.log |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| * (m.totient : ℝ) = (Module.finrank ℚ L : ℝ) * vonMangoldt m := by
  have hm0 : 0 < m := by omega
  have hint_r : IsIntegral ℚ η := .of_finite ℚ η
  have hx : IsIntegral ℚ (η - 1) := .of_finite ℚ _
  have hmin : minpoly ℚ (η - 1) = (cyclotomic m ℚ).comp (X + C 1) := by
    have h0 : minpoly ℚ (η - algebraMap ℚ L 1) = (minpoly ℚ η).comp (X + C 1) := by
      exact minpoly.sub_algebraMap η (1 : ℚ)
    rw [map_one] at h0
    rw [h0, ← cyclotomic_eq_minpoly_rat hη hm0]
  have hdeg : Module.finrank ℚ ℚ⟮η - 1⟯ = m.totient := by
    rw [IntermediateField.adjoin.finrank hx, hmin, natDegree_comp, natDegree_cyclotomic, natDegree_X_add_C,
      mul_one]
  have hnormval : Algebra.norm ℚ (η - 1) =
      ((-1) ^ m.totient * eval 1 (cyclotomic m ℚ)) ^ Module.finrank ℚ⟮η - 1⟯ L := by
    rw [Algebra.norm_eq_norm_adjoin ℚ (η - 1)]
    congr 1
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_dim] at h
    rw [show IntermediateField.AdjoinSimple.gen ℚ (η - 1) = (IntermediateField.adjoin.powerBasis hx).gen from rfl,
      h, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin, coeff_zero_eq_eval_zero,
      eval_comp, natDegree_comp, natDegree_cyclotomic, natDegree_X_add_C, mul_one]
    simp
  have habs : |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| =
      |((eval 1 (cyclotomic m ℚ) : ℚ) : ℝ)| ^ Module.finrank ℚ⟮η - 1⟯ L := by
    rw [hnormval]; push_cast; rw [abs_pow, abs_mul, abs_pow]; simp
  haveI : Module.Free ℚ ℚ⟮η - 1⟯ := Module.Free.of_divisionRing _ _
  rw [habs, Real.log_pow, log_abs_eval_one_cyclotomic_eq_vonMangoldt hm, ← Module.finrank_mul_finrank ℚ ℚ⟮η - 1⟯ L, hdeg]
  push_cast; ring
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
omit E
namespace Formalism.HC.Der.Rd
theorem _root_.solution (u : ZMod N) (hu : u ≠ 1) :
    Real.log |((Algebra.norm ℚ (ζ - ζ ^ u.val) : ℚ) : ℝ)| =
      (N.totient : ℝ) * (vonMangoldt (addOrderOf (u - 1)) / ((addOrderOf (u - 1)).totient : ℝ)) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hw : (1 - u).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero, sub_eq_zero]; exact Ne.symm hu
  have hmod : ζ ^ (u.val + (1 - u).val) = ζ := by
    have h1 : (u.val + (1 - u).val) % orderOf ζ = 1 % orderOf ζ := by
      rw [← hζ.eq_orderOf, ← ZMod.val_add, show u + (1 - u) = 1 by ring, ZMod.val_one_eq_one_mod]
    rw [← pow_mod_orderOf, h1, pow_mod_orderOf, pow_one]
  have hfac : ζ - ζ ^ u.val = ζ ^ u.val * (ζ ^ (1 - u).val - 1) := by
    calc ζ - ζ ^ u.val = ζ ^ (u.val + (1 - u).val) - ζ ^ u.val := by rw [hmod]
      _ = ζ ^ u.val * (ζ ^ (1 - u).val - 1) := by ring
  have hnz : |((Algebra.norm ℚ ζ : ℚ) : ℝ)| = 1 := by
    have h : (Algebra.norm ℚ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have h' : |((Algebra.norm ℚ ζ : ℚ) : ℝ)| ^ N = 1 := by
      rw [← abs_pow, ← Rat.cast_pow, h, Rat.cast_one, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hN).1 h'
  have hd : orderOf (ζ ^ (1 - u).val) = addOrderOf (u - 1) := by
    rw [orderOf_pow' ζ hw, ← hζ.eq_orderOf,
      show u - 1 = -(((1 - u).val : ℕ) : ZMod N) by rw [ZMod.natCast_zmod_val]; ring,
      addOrderOf_neg, ZMod.addOrderOf_coe _ hN]
  have hη : IsPrimitiveRoot (ζ ^ (1 - u).val) (addOrderOf (u - 1)) := by
    rw [← hd]; exact IsPrimitiveRoot.orderOf _
  have hd1 : 1 < addOrderOf (u - 1) := by
    have h0 : 0 < addOrderOf (u - 1) := addOrderOf_pos _
    have h1 : addOrderOf (u - 1) ≠ 1 := by
      intro h
      have := addOrderOf_nsmul_eq_zero (u - 1)
      rw [h, one_nsmul, sub_eq_zero] at this
      exact hu this
    omega
  have key := log_abs_norm_sub_one_mul_totient_eq hd1 hη
  rw [IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (NeZero.pos N))] at key
  rw [hfac, map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow, hnz, one_pow, one_mul]
  have ht : (0 : ℝ) < (addOrderOf (u - 1)).totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [mul_div_assoc', eq_div_iff ht.ne']
  exact key
end Formalism.HC.Der.Rd
