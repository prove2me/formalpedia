-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:05.095477+00:00
-- url     : https://prove2.me/submissions/9e0fb0ad-5b0f-4147-bef0-5feedb8381ff

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
variable {a b : ℕ}
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b)
    (i : Fin a) : shuffle J h hc (Fin.castAdd b i) = J.orderEmbOfFin h i := by
  simp [shuffle]
end Formalism.ResultantValuation.LaplaceProof
