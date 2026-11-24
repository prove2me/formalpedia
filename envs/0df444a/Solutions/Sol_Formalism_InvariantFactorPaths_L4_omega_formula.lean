-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.omega_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:16.587033+00:00
-- url     : https://prove2.me/submissions/03158526-b52c-41b0-895f-15ad0edfe226

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eW_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eul_pderiv
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_mem
import Theorems.Thm_Formalism_CountingSumsFrames_pol_iff_eul
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_disj_last
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_mem
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (ρ : Fin r) (c : ℤ) (o : ℕ)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hP : x ∈ Pol p r (setLast LL (o + 1)))
    (hF : x ∈ FreeOf p (Fin.last K, ρ)) :
    Omega p LL c ρ x = (((c - o) * (o + 1) : ℤ) : ℚ_[p]) • x -
      ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ, eW p K b a (glAct p LL K a b x) := by
  have hsum : ∑ a ∈ univ.erase ρ, X (Fin.last K, a) * pderiv (Fin.last K, a) x = ((o + 1 : ℕ) : ℚ_[p]) • x := by
    have h1 := (pol_iff_eul _ x).mp hP (Fin.last K)
    have h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1 := by simp [setLast]
    rw [h2, ProjS.eulL_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), pderiv_free _ x hF, mul_zero,
      zero_add] at h1
    exact h1
  have hterm : ∀ a : Fin r, Uop p LL c (univ.erase ρ) a (dW p K a x) =
      (((c - o : ℤ)) : ℚ_[p]) • (X (Fin.last K, a) * pderiv (Fin.last K, a) x) -
        ∑ b ∈ univ.erase ρ, eW p K b a (glAct p LL K a b x) := by
    intro a
    rw [Uop_apply]
    have e0 : dW p K a x = pderiv (Fin.last K, a) x := rfl
    rw [e0, eul_pderiv LL o a x hP, ← sub_smul, mul_smul_comm]
    congr 1
    · congr 1; push_cast; ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [eW_apply]
      congr 1
      exact (FockB.ops_apply_comm disj_last (FockB.pderiv_mem (last_mem a)) (glAct_mem LL K a b) x).symm
  unfold Omega
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, hterm]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hsum, smul_smul]
  congr 2
  push_cast
  ring
end Formalism.InvariantFactorPaths.L4
