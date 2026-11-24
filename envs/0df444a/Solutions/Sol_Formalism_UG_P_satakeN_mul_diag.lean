-- Prove2me | solution 1 for Formalism.UG.P.satakeN_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:41.491804+00:00
-- url     : https://prove2.me/submissions/fee6e595-d263-41a5-a9e2-3430b93f6c80

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (S S' : Finset (Fin n)) (c : satakePairs S → O) (c' : satakePairs S' → O)
    (a : Fin n) : (satakeN O S c * satakeN O S' c') a a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hab : a < b
  · rw [satakeN_apply O S' c' b a, dif_neg (fun h => absurd h.2.2 (lt_asymm hab)), mul_zero]
  · rw [satakeN_apply O S c a b, dif_neg (fun h => hab h.2.2), zero_mul]
end Formalism.UG.P
