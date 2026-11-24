-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.ops_ycond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:56.290069+00:00
-- url     : https://prove2.me/submissions/9da6799c-3c20-4bf3-83e8-d6e009ec7aed

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_mem
import Theorems.Thm_Formalism_CountingSumsFrames_ops_keep_supp
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_keep
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (T : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hT : T ∈ FockB.Ops {v : Fin N × Fin r | j ≤ (v.1 : ℕ)}) :
    ∀ x ∈ YCond p LL j Mt, T x ∈ YCond p LL j Mt := by
  have hdisj : Disjoint {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} {v : Fin N × Fin r | (v.1 : ℕ) < j} := by
    rw [Set.disjoint_left]; rintro v h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2; omega
  intro x hx
  refine ycond_keep LL j Mt T
    (fun a b y => FockB.ops_apply_comm hdisj hT (glAct_mem LL j a b) y)
    (fun y hy => ops_keep_supp {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} _ (fun m m' hmm hm => ?_) hT y hy) x hx
  have : wt LL j 0 m = wt LL j 0 m' :=
    wt_congr LL j 0 m m' (fun i hi => hmm (i, 0) (by simp only [Set.mem_ofPred_eq]; omega))
  simp only [Set.mem_ofPred_eq] at hm ⊢
  rw [← this]; exact hm
end Formalism.InvariantFactorPaths.L4
