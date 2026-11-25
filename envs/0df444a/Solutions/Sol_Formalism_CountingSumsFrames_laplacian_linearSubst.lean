-- Prove2me | solution 1 for Formalism.CountingSumsFrames.laplacian_linearSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:55.788346+00:00
-- url     : https://prove2.me/submissions/94ba313e-e2fc-4958-914a-bf7df64c12e6

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_pderiv_inl_linearSubst
import Theorems.Thm_Formalism_CountingSumsFrames_pderiv_inr_linearSubst
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_laplacian_apply__7d05e53cfbcb

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
theorem _root_.solution (g : GL (Fin k) K) (f : PolXY K k) : ctrF K k (glAct g f) = glAct g (ctrF K k f) := by
  have hg : (g : Matrix (Fin k) (Fin k) K) * ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul]; simp
  rw [laplacian_apply', laplacian_apply', map_sum]
  simp only [pderiv_inr_linearSubst, map_sum, pderiv_C_mul, pderiv_inl_linearSubst, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ l : Fin k, ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) *
        (C ((g : Matrix (Fin k) (Fin k) K) l j) * glAct g (pderiv (Sum.inl l) (pderiv (Sum.inr i) f))) =
      C ((1 : Matrix (Fin k) (Fin k) K) l i) * glAct g (pderiv (Sum.inl l) (pderiv (Sum.inr i) f)) := by
    intro l
    rw [← hg, Matrix.mul_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [C_mul]; ring
  simp only [this, Matrix.one_apply]
  simp [Finset.sum_ite_eq']
end Formalism.CountingSumsFrames
