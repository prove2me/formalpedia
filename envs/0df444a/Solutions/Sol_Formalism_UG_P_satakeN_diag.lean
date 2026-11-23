-- Prove2me | solution 1 for Formalism.UG.P.satakeN_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:07.445435+00:00
-- url     : https://prove2.me/submissions/383fa02c-68e0-424c-af08-2d638e2d2ebb

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
theorem _root_.solution (S : Finset (Fin n)) (c : satakePairs S → O) (a : Fin n) :
    satakeN O S c a a = 0 := by
  rw [satakeN_apply, dif_neg (fun h => lt_irrefl a h.2.2)]
end Formalism.UG.P
