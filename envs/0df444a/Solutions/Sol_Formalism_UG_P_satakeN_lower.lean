-- Prove2me | solution 1 for Formalism.UG.P.satakeN_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:51.418459+00:00
-- url     : https://prove2.me/submissions/74647074-3054-45d4-8edf-58e26fec544b

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
theorem _root_.solution (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) (h : l < a) :
    satakeN O S c a l = 0 := by
  rw [satakeN_apply, dif_neg (fun h' => absurd h'.2.2 (lt_asymm h))]
end Formalism.UG.P
