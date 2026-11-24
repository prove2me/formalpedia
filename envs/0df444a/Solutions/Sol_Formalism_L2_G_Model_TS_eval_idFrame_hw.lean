-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.eval_idFrame_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:59:34.821549+00:00
-- url     : https://prove2.me/submissions/fa7d13ae-4377-4d76-9121-f592d314222f

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingHighestWeightProof
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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow]
  have h := eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega)
  change eval (idPoint R r n) _ ^ _ = 1
  rw [h, one_pow]
end Formalism.L2.G.Model.TS
