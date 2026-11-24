-- Prove2me | solution 1 for Formalism.UG.P.satakeU_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:08.595238+00:00
-- url     : https://prove2.me/submissions/09099df8-eaad-472c-85d7-a5dfd365fba7

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Theorems.Thm_Formalism_UG_P_satakeN_mem
import Theorems.Thm_Formalism_UG_P_satake_mem_glint

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
variable {O}
variable (O)
namespace Formalism.UG.P
theorem _root_.solution (S : Finset (Fin n)) (c : satakePairs S → O) : satakeU O S c ∈ GLint (Fin n) O := by
  refine satake_mem_glint O _ (fun a b => ?_) (fun a b => ?_)
  · show (1 + satakeN O S c) a b ∈ O
    rw [Matrix.add_apply, Matrix.one_apply]
    exact O.add_mem (by split_ifs; exacts [O.one_mem, O.zero_mem]) (satakeN_mem O S c a b)
  · show (1 - satakeN O S c) a b ∈ O
    rw [Matrix.sub_apply, Matrix.one_apply]
    exact O.sub_mem (by split_ifs; exacts [O.one_mem, O.zero_mem]) (satakeN_mem O S c a b)
end Formalism.UG.P
