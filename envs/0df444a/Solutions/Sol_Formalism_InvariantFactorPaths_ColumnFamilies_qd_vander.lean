-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_vander
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:52.133556+00:00
-- url     : https://prove2.me/submissions/b2f53167-11e3-4b89-8c36-b33c000f8d52

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {σ : Type} (W : Submodule ℚ (MvPolynomial σ ℚ)) (p : Polynomial (MvPolynomial σ ℚ))
    (h : ∀ t : ℕ, p.eval (C (t : ℚ)) ∈ W) (k : ℕ) : p.coeff k ∈ W := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro φ
  set ψ : MvPolynomial σ ℚ →ₗ[ℚ] ℚ := φ ∘ₗ W.mkQ with hψ
  have hW : ∀ x ∈ W, ψ x = 0 := by
    intro x hx
    rw [hψ, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hx, map_zero]
  set q : Polynomial ℚ := ∑ i ∈ range (p.natDegree + 1), Polynomial.monomial i (ψ (p.coeff i)) with hq
  have hev : ∀ t : ℕ, q.eval (t : ℚ) = 0 := by
    intro t
    rw [← hW _ (h t), Polynomial.eval_eq_sum_range (p := p), map_sum, hq, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial, ← map_pow, mul_comm (p.coeff i), ← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range (fun t : ℕ => (t : ℚ)))
    · rintro _ ⟨t, rfl⟩
      exact hev t
    · exact Set.infinite_range_of_injective Nat.cast_injective
  have hc : q.coeff k = ψ (p.coeff k) := by
    rw [hq, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' ]
    split_ifs with hk
    · rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk), map_zero]
  rw [hq0, Polynomial.coeff_zero] at hc
  exact hc.symm
end Formalism.InvariantFactorPaths.ColumnFamilies
