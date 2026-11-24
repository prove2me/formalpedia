-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:18.448577+00:00
-- url     : https://prove2.me/submissions/b5cf9698-68dd-4138-8bb9-cc6c592cca0f

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
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
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hv : LL.vec (Fin.last K) = true) (ρ c d : Fin r) (hd : d ≠ ρ) (e : ℕ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) c d (X (Fin.last K, ρ) ^ e * h) = X (Fin.last K, ρ) ^ e * glAct p LL (K + 1) c d h := by
  have hd0 : ∀ (i : Fin (K + 1)) (b : Fin r), (i, b) ≠ (Fin.last K, ρ) →
      pderiv (i, b) (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) = 0 := by
    intro i b hne
    rw [Derivation.leibniz_pow, pderiv_X_of_ne (Ne.symm hne), smul_zero, smul_zero]
  unfold glAct
  simp only [LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h1 h2
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [Derivation.leibniz, hd0 i d (fun h => hd (Prod.mk.inj h).2), smul_zero, add_zero, smul_eq_mul]
    ring
  · have hi : i ≠ Fin.last K := by
      rintro rfl
      rw [hv] at h2
      exact h2 rfl
    simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [Derivation.leibniz, hd0 i c (fun h => hi (Prod.mk.inj h).1), smul_zero, add_zero, smul_eq_mul]
    ring
  · simp
end Formalism.InvariantFactorPaths.L4
