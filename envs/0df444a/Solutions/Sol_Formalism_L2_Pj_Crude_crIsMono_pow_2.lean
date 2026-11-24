-- Prove2me | solution 2 for Formalism.L2.Pj.Crude.crIsMono_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:51.978731+00:00
-- url     : https://prove2.me/submissions/845af876-89b8-447b-b833-78ff2439581c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_one

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
theorem _root_.solution {R : Type} [CommRing R] {p : MvPolynomial (Letter T r n) R} (hp : crIsMono p)
    (e : ℕ) : crIsMono (p ^ e) := by
  induction e with
  | zero =>
    rw [pow_zero]
    exact crIsMono_one
  | succ e ih =>
    rw [pow_succ]
    exact crIsMono_mul ih hp
end Formalism.L2.Pj.Crude
