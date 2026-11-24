-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.perm_sign_eq_inversion_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:45.184071+00:00
-- url     : https://prove2.me/submissions/d8750039-ff2d-4b4d-ab0a-193aef364058

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution {n : ℕ} (f : Perm (Fin n)) : Perm.sign f = Perm.signAux f := by
  refine Perm.swap_induction_on f ?_ ?_
  · rw [map_one, Perm.signAux_one]
  · intro g x y hxy ih
    rw [Perm.sign_mul, Perm.signAux_mul, ih, Perm.sign_swap hxy, Perm.signAux_swap hxy]
end Formalism.ResultantValuation.LaplaceProof
