-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glRest_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:36.660085+00:00
-- url     : https://prove2.me/submissions/b8b91af6-c6ca-4f43-a6e9-8175da053279

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_GM_FockB_mulLeftX_mem
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j j' : ℕ) (hjj : j ≤ j') (c d : Fin r) :
    (glRest p LL j j' c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} := by
  show (glAct p LL j' c d - glAct p LL j c d : Module.End ℚ_[p] _) ∈ _
  unfold glAct
  rw [← Finset.sum_sub_distrib]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  by_cases h1 : (i : ℕ) < j
  · have h2 : (i : ℕ) < j' := lt_of_lt_of_le h1 hjj
    simp only [if_pos h1, if_pos h2, sub_self]
    exact Subalgebra.zero_mem _
  · have hm : ∀ e : Fin r, (i, e) ∈ {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} := fun e => not_lt.mp h1
    by_cases h2 : (i : ℕ) < j'
    · simp only [if_pos h2, if_neg h1, sub_zero]
      split_ifs
      · exact Subalgebra.mul_mem _ (FockB.mulLeftX_mem (hm c)) (FockB.pderiv_mem (hm d))
      · exact Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (FockB.mulLeftX_mem (hm d)) (FockB.pderiv_mem (hm c)))
    · simp only [if_neg h2, if_neg h1, sub_zero]
      exact Subalgebra.zero_mem _
end Formalism.InvariantFactorPaths.L4
