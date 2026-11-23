-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resL_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:07.886839+00:00
-- url     : https://prove2.me/submissions/a1db2075-fb79-4eaa-af5e-64d39da19b15

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_X_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_pderiv
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) (e : ℕ)
    (h : ∀ i : Fin N, (i : ℕ) < j → (i, c) ≠ v ∧ (i, d) ≠ v) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p v e (glAct p LL j c d x) = glAct p LL j c d (resL p v e x) := by
  classical
  rw [glAct, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : (i : ℕ) < j
  · obtain ⟨hc, hd⟩ := h i hij
    by_cases hv : LL.vec i
    · simp only [hij, hv, if_true, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [resL_X_mul v (i, c) hc]
      exact congrArg (X (i, c) * ·) (resL_pderiv v (i, d) hd e x)
    · simp only [hij, hv, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, map_neg]
      rw [resL_X_mul v (i, d) hd]
      exact congrArg (fun y => -(X (i, d) * y)) (resL_pderiv v (i, c) hc e x)
  · simp [hij]
end Formalism.InvariantFactorPaths.L4
