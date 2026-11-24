-- Prove2me | solution 1 for Formalism.UG.P.satakeN_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:51.99822+00:00
-- url     : https://prove2.me/submissions/38e0f9dc-3c96-4d70-8f3c-e4c878eb7bb1

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
theorem _root_.solution (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) :
    satakeN O S c a l ∈ O := by
  rw [satakeN_apply]
  split_ifs with h
  · exact (c ⟨(a, l), h⟩).2
  · exact O.zero_mem
end Formalism.UG.P
