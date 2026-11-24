-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.free_ycond_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:49:18.825852+00:00
-- url     : https://prove2.me/submissions/1593762d-667a-4323-b9e3-968a7a2c23ae

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_mem
import Theorems.Thm_Formalism_CountingSumsFrames_ops_keep_supp
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycond
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_freeLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_succ
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
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ) :
    YCond p LL K Mt ⊓ FreeLast p K r ≤ YCond p LL (K + 1) Mt := by
  refine le_ycond LL (K + 1) Mt _ ?_ ?_
  · intro x hx
    have h1 := ycond_le_supp LL K Mt (Submodule.mem_inf.mp hx).1
    have h2 := (Submodule.mem_inf.mp hx).2
    rw [FreeLast, mem_restrictSupport_iff] at h2
    rw [mem_restrictSupport_iff] at h1 ⊢
    intro m hm
    have h3 := h1 hm
    have h4 := h2 hm 0
    simp only [Set.mem_ofPred_eq] at h3 ⊢
    rw [wt_succ LL hv, h4]
    simpa using h3
  · intro c d x hx
    have h2 := (Submodule.mem_inf.mp hx).2
    have e : glAct p LL (K + 1) c d x = glAct p LL K c d x := by
      rw [glAct_succ LL hv, pderiv_freeLast x h2 d, mul_zero, add_zero]
    rw [e]
    refine Submodule.mem_inf.mpr ⟨ycond_glStable LL K Mt c d x (Submodule.mem_inf.mp hx).1, ?_⟩
    refine ops_keep_supp {v : Fin (K + 1) × Fin r | (v.1 : ℕ) < K}
      {m : Fin (K + 1) × Fin r →₀ ℕ | ∀ c, m (Fin.last K, c) = 0} (fun m m' hmm hm c' => ?_)
      (glAct_mem LL K c d) x h2
    rw [← hmm (Fin.last K, c') (by simp only [Set.mem_ofPred_eq, Fin.val_last, lt_irrefl, not_false_eq_true])]
    exact hm c'
end Formalism.InvariantFactorPaths.L4
