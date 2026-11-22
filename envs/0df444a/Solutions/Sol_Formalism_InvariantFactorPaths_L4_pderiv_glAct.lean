-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pderiv_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:38:17.125157+00:00
-- url     : https://prove2.me/submissions/a0e37d7f-b325-498c-ab10-67a56210cde8

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_ne_of_lt
import Theorems.Thm_Formalism_GM_ProjS_pderiv_comm
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


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section Res
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end Res
section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
private theorem pderiv_last_glAct_comm (LL : Letters (K + 1)) (a b c : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, c) (glAct p LL K a b x) = glAct p LL K a b (pderiv (Fin.last K, c) x) := by
  classical
  rw [glAct, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : (i : ℕ) < K
  · have hne : ∀ d : Fin r, ((i, d) : Fin (K + 1) × Fin r) ≠ (Fin.last K, c) :=
      fun d h => last_ne_of_lt i hij (congrArg Prod.fst h).symm
    by_cases hv : LL.vec i
    · simp only [hij, hv, if_true, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (hne a), smul_zero, add_zero, smul_eq_mul]
      exact congrArg (X (i, a) * ·) (Formalism.GM.ProjS.pderiv_comm (Fin.last K, c) (i, b) x)
    · simp only [hij, hv, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, map_neg]
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (hne b), smul_zero, add_zero, smul_eq_mul]
      exact congrArg (fun y => -(X (i, b) * y)) (Formalism.GM.ProjS.pderiv_comm (Fin.last K, c) (i, a) x)
  · simp [hij]
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (a b c : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, c) (glAct p LL (K + 1) a b x) =
      glAct p LL (K + 1) a b (pderiv (Fin.last K, c) x) + (if a = c then pderiv (Fin.last K, b) x else 0) := by
  classical
  rw [glAct_succ LL hv, glAct_succ LL hv, map_add, pderiv_last_glAct_comm, Derivation.leibniz,
    MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul,
    Formalism.GM.ProjS.pderiv_comm (Fin.last K, c) (Fin.last K, b) x]
  by_cases hac : a = c
  · subst hac
    simp only [Pi.single_eq_same, mul_one, if_true]
    ring
  · simp [Pi.single_apply, hac, add_assoc]
end Formalism.InvariantFactorPaths.L4
