-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crDiagExp_dl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:21:22.696199+00:00
-- url     : https://prove2.me/submissions/a980d88d-c754-4288-a08d-5159ef8c1633

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crDl_inj
import Theorems.Thm_Formalism_L2_Pj_Crude_crDiagExp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (p : Σ σ : T, Fin (r σ)) :
    diagExp r n β a (crDl β p) = a p.1 p.2 := by
  rw [crDiagExp_apply, Finset.sum_eq_single p]
  · rw [if_pos rfl]
  · intro q _ hq
    exact if_neg (fun h => hq (crDl_inj β h))
  · intro h
    exact absurd (Finset.mem_univ p) h
end Formalism.L2.Pj.Crude
