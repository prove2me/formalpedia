-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.finrank_span_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:57.68602+00:00
-- url     : https://prove2.me/submissions/31944f1a-4f4e-4370-8741-ab76041d3807

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a m : ℕ} (x : Fin a → TruncK K' n) (hx : (TT) ^ m • x = 0) :
    Module.finrank K' ↥(Submodule.span (TruncK K' n) {x}) ≤ m := by
  have hle : (Submodule.span (TruncK K' n) {x}).restrictScalars K' ≤
      Submodule.span K' (Set.range (fun j : Fin m => (TT) ^ (j : ℕ) • x)) := by
    intro y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, add_smul]
      exact Submodule.add_mem _ (hp (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
        (hq (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
    | monomial j c =>
      have e : (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) (monomial j c) : TruncK K' n) =
          algebraMap K' (TruncK K' n) c * (TT) ^ j := by
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
        rfl
      rw [e, mul_smul, algebraMap_smul]
      apply Submodule.smul_mem
      by_cases hj : j < m
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      · rw [← Nat.sub_add_cancel (not_lt.mp hj), pow_add, mul_smul, hx, smul_zero]
        exact Submodule.zero_mem _
  calc Module.finrank K' ↥(Submodule.span (TruncK K' n) {x})
      = Module.finrank K' ↥((Submodule.span (TruncK K' n) {x}).restrictScalars K') := rfl
    _ ≤ Module.finrank K' ↥(Submodule.span K' (Set.range (fun j : Fin m => (TT) ^ (j : ℕ) • x))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin m) := finrank_range_le_card _
    _ = m := Fintype.card_fin m
end Formalism.CyclotomicNorms.residueMatrixData
