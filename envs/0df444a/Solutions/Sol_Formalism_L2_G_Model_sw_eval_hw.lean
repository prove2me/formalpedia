-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_eval_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:34.192419+00:00
-- url     : https://prove2.me/submissions/1654c05b-641f-4d7b-bfe7-97a9e308186e

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_eval_idPoint_lpMinor


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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idPoint R r n) (hw R hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega), one_pow]
end Formalism.L2.G.Model
