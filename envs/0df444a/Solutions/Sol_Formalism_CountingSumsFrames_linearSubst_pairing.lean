-- Prove2me | solution 1 for Formalism.CountingSumsFrames.linearSubst_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:54.250991+00:00
-- url     : https://prove2.me/submissions/9264950f-ec57-4f6e-9bba-b3065929b81f

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (g : GL (Fin k) K) : glAct g (hXY K k) = hXY K k := by
  have hg : ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) * (g : Matrix (Fin k) (Fin k) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul]; simp
  simp only [glAct, hXY, map_sum, map_mul, aeval_X, Sum.elim_inl, Sum.elim_inr]
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  have : ∀ l : Fin k, ∑ i : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j) *
      (C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) * X (Sum.inr l)) =
      C ((1 : Matrix (Fin k) (Fin k) K) l j) * ((X (Sum.inl j) : PolXY K k) * X (Sum.inr l)) := by
    intro l
    rw [← hg, Matrix.mul_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [C_mul]; ring
  simp only [this, Matrix.one_apply]
  simp [Finset.sum_ite_eq']
end Formalism.CountingSumsFrames
