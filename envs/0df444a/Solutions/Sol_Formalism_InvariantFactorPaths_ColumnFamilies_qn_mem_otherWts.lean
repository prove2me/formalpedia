-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_mem_otherWts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:44:38.135543+00:00
-- url     : https://prove2.me/submissions/888f777f-6ab4-47ff-be2b-401e9af27960

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_monomial_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (lam : Fin n → ℤ) (g : MvPolynomial (Fin n × Fin n) ℚ)
    (hg : ∀ m ∈ g.support, qn_wt m ≠ lam) : g ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) lam := by
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  unfold otherWts
  exact Submodule.mem_iSup_of_mem (qn_wt m) (Submodule.mem_iSup_of_mem (hg m hm) (qn_monomial_mem n m _))
end Formalism.InvariantFactorPaths.ColumnFamilies
