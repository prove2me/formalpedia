-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.Pmin_coeff_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:58.405395+00:00
-- url     : https://prove2.me/submissions/99f52838-5a29-4976-b512-e0cc316203b6

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_map
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_coeff_diag

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
variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (hβ : Function.Injective β) (ha : Dom r a) :
    (MvPolynomial.map (Int.castRingHom k) (Pmin r n β a)).coeff (diagExp r n β a) = 1 := by
  rw [crP_map]
  exact crP_coeff_diag k β a hβ ha
end Formalism.L2.Pj.Crude
