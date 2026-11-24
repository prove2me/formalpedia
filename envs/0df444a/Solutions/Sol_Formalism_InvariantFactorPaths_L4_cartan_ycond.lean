-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.cartan_ycond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.931682+00:00
-- url     : https://prove2.me/submissions/5b1c075c-aa3c-4923-bca6-da17a6fd4e83

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_CountingSumsFrames_ops_keep_supp
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_keep
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_split
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glRest_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glRest_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_congr
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters N) (j' j : ℕ) (hjj : j' ≤ j) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL j' Mt, glAct p LL j c c x ∈ YCond p LL j' Mt := by
  intro x hx
  rw [glAct_split LL j' j c c, LinearMap.add_apply]
  refine Submodule.add_mem _ (ycond_glStable LL j' Mt c c x hx) ?_
  refine ycond_keep LL j' Mt (glRest p LL j' j c c) (fun a b y => glRest_comm LL j' j hjj c c a b y)
    (fun y hy => ops_keep_supp {v : Fin N × Fin r | j' ≤ (v.1 : ℕ)} _ (fun m m' hmm hm => ?_)
      (glRest_mem LL j' j hjj c c) y hy) x hx
  have : wt LL j' 0 m = wt LL j' 0 m' :=
    wt_congr LL j' 0 m m' (fun i hi => hmm (i, 0) (by simp only [Set.mem_ofPred_eq]; omega))
  simp only [Set.mem_ofPred_eq] at hm ⊢
  rw [← this]; exact hm
end Formalism.InvariantFactorPaths.L4
