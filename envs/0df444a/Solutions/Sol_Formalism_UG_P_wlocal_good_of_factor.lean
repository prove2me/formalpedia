-- Prove2me | solution 1 for Formalism.UG.P.wlocal_good_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:59.680808+00:00
-- url     : https://prove2.me/submissions/874b87e4-9eca-4036-a221-d76dc53723a6

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_good_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution {r n : ℕ} {hn : n ≤ r} {ν : Fin n → ℕ} {M Q Q' : Matrix (Fin r) (Fin r) R}
    (hQ : wlocal_Good hn ν Q) (hQQ : Q * Q' = 1) (h : wlocal_Good hn ν (Q' * M)) :
    wlocal_Good hn ν M := by
  have hM : M = Q * (Q' * M) := by
    rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  rw [hM]
  exact wlocal_good_mul hQ h
end Formalism.UG.P
