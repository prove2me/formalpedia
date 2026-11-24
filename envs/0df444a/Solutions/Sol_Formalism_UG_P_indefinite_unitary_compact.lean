-- Prove2me | solution 1 for Formalism.UG.P.indefinite_unitary_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:06:32.750234+00:00
-- url     : https://prove2.me/submissions/d8a86130-5a9f-403b-8521-a98123320466

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Theorems.Thm_Formalism_UG_P_isCompact_units_of_unitary
import Theorems.Thm_Formalism_UG_P_mem_Upq_iff
import Theorems.Thm_Formalism_UG_P_Jpq_zero

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
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.UpqCompact := by
  intro p
  have hT : IsClosed {M : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ | star M * M = 1} :=
    isClosed_eq (continuous_star.mul continuous_id) continuous_const
  have h := isCompact_units_of_unitary hT (fun M hM => hM)
  convert h using 1
  ext g
  simp only [SetLike.mem_coe, mem_Upq_iff, Jpq_zero, mul_one, Set.mem_setOf_eq]
end Formalism.UG.P
