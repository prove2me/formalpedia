-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crDiagExp_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:49.229387+00:00
-- url     : https://prove2.me/submissions/be5740cd-09e1-482b-a21b-7fd2584f0099

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
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
theorem _root_.solution (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (ℓ : Letter T r n)
    (h : ∀ p, crDl β p ≠ ℓ) : diagExp r n β a ℓ = 0 := by
  rw [crDiagExp_apply]
  exact Finset.sum_eq_zero fun p _ => if_neg (h p)
end Formalism.L2.Pj.Crude
