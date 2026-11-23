-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pderiv_inl_linearSubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:24.308393+00:00
-- url     : https://prove2.me/submissions/cabd5084-ba97-4767-ad4d-c14dae929435

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_pderiv_aeval_eq_sum_chain_rule

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
theorem _root_.solution (g : GL (Fin k) K) (j : Fin k) (f : PolXY K k) :
    pderiv (Sum.inl j) (glAct g f) =
      ∑ i : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * glAct g (pderiv (Sum.inl i) f) := by
  classical
  unfold glAct
  rw [pderiv_aeval_eq_sum_chain_rule, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply]
  simp [mul_comm]
end Formalism.CountingSumsFrames
