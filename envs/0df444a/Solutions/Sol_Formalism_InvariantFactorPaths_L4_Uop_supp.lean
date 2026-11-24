-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Uop_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.624618+00:00
-- url     : https://prove2.me/submissions/eb950b58-93e7-460e-a805-d3d36e6d95d0

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eulL_keep_supp
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_keep
import Theorems.Thm_Formalism_CountingSumsFrames_wt_shift
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_wt
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
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c k : ℤ)
    (Cs : Finset (Fin r)) (a : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hF : F ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ k}) :
    Uop p LL c Cs a F ∈ restrictSupport ℚ_[p]
      {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ k + (if a = 0 then 1 else 0)} := by
  rw [Uop_apply]
  refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun b _ => ?_)
  · rw [X_mul_mem p]
    refine restrictSupport_mono ℚ_[p] ?_ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) (eulL_keep_supp _ _ F hF))
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [last_wt LL (K + 1) le_rfl hv]
    omega
  · rw [X_mul_mem p]
    refine glAct_keep LL K a b _ _ ?_ ?_ F hF
    · intro i hi hvi m hm hb
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [last_wt LL (K + 1) le_rfl hv, (wt_shift LL (K + 1) a b 0 i (by omega) m).1 hvi hb]
      omega
    · intro i hi hvi m hm hb
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [last_wt LL (K + 1) le_rfl hv, (wt_shift LL (K + 1) a b 0 i (by omega) m).2 hvi hb]
      omega
end Formalism.InvariantFactorPaths.L4
