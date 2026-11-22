-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:32:51.066053+00:00
-- url     : https://prove2.me/submissions/4a0f9f04-8e85-4854-abb8-9d8f2a190a8e

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd

set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
variable {a b : ℕ}
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b)
    (j : Fin b) : shuffle J h hc (Fin.natAdd a j) = Jᶜ.orderEmbOfFin hc j := by
  simp [shuffle]
end Formalism.ResultantValuation.LaplaceProof
