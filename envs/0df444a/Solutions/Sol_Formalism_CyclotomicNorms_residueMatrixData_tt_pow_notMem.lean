-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.tt_pow_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:52.435006+00:00
-- url     : https://prove2.me/submissions/f7b760bf-11f8-4fda-82b3-40e77a9dc06e

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
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
theorem _root_.solution {m C : ℕ} (hm : m ≤ C) (hC : C < n) :
    (TT) ^ m ∉ Ideal.span {(TT) ^ (C + 1)} := by
  rw [Ideal.mem_span_singleton]
  rintro ⟨y, hy⟩
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_pow, ← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hy
  have h1 : (X : K'[X]) ^ (C + 1) ∣ X ^ m - X ^ (C + 1) * q :=
    (pow_dvd_pow X (by omega : C + 1 ≤ n)).trans hy
  have h2 : (X : K'[X]) ^ (C + 1) ∣ X ^ m := by
    have := h1.add (dvd_mul_right ((X : K'[X]) ^ (C + 1)) q)
    simpa using this
  rw [Polynomial.X_pow_dvd_iff] at h2
  have := h2 m (by omega)
  rw [Polynomial.coeff_X_pow_self] at this
  exact one_ne_zero this
end Formalism.CyclotomicNorms.residueMatrixData
