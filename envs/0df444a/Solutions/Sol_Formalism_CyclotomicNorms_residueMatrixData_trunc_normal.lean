-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.trunc_normal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:08.650137+00:00
-- url     : https://prove2.me/submissions/4e342830-e4f2-47e8-ac5a-13cea1013613

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_pow_n
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_pow_ge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_succ
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_succ

set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution (x : TruncK K' n) : ∃ k ≤ n, ∃ u : TruncK K' n, IsUnit u ∧ x = u * (TT) ^ k := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  by_cases hp : p = 0
  · exact ⟨n, le_rfl, 1, isUnit_one, by simp [hp, tt_pow_n]⟩
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  simp only [map_zero, sub_zero] at hpq hq
  set m := rootMultiplicity 0 p
  by_cases hm : n ≤ m
  · refine ⟨n, le_rfl, 1, isUnit_one, ?_⟩
    rw [hpq, map_mul, map_pow, tt_pow_ge hm, tt_pow_n]; simp
  · replace hm := not_le.mp hm
    refine ⟨m, hm.le, Ideal.Quotient.mk _ q, ?_, ?_⟩
    · have hc : IsCoprime ((X : K'[X]) ^ n) q :=
        IsCoprime.pow_left ((Polynomial.irreducible_X).coprime_iff_not_dvd.mpr hq)
      obtain ⟨u, v, huv⟩ := hc
      refine isUnit_iff_exists_inv'.mpr ⟨Ideal.Quotient.mk _ v, ?_⟩
      have : Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) (u * X ^ n + v * q) = 1 := by
        rw [huv, map_one]
      rw [map_add, map_mul, map_mul, map_pow, tt_pow_n, mul_zero, zero_add] at this
      exact this
    · rw [hpq, map_mul, map_pow, mul_comm]
end Formalism.CyclotomicNorms.residueMatrixData
