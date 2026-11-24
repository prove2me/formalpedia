-- Prove2me | solution 1 for Formalism.UG.P.permMatrix_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:44.461998+00:00
-- url     : https://prove2.me/submissions/e86b9b6a-6733-44af-8660-08acc0b27b37

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
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
theorem _root_.solution (σ : Equiv.Perm (Fin n)) : satakeP (L := L) σ ∈ GLint (Fin n) O := by
  refine satake_mem_glint O _ (fun a b => ?_) (fun a b => ?_)
  · show σ.toPEquiv.toMatrix a b ∈ O
    rw [PEquiv.toMatrix_apply]
    split_ifs
    exacts [O.one_mem, O.zero_mem]
  · show σ.symm.toPEquiv.toMatrix a b ∈ O
    rw [PEquiv.toMatrix_apply]
    split_ifs
    exacts [O.one_mem, O.zero_mem]
end Formalism.UG.P
