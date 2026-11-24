-- Prove2me | solution 1 for Formalism.UG.P.linSubst_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:57.386275+00:00
-- url     : https://prove2.me/submissions/45457024-755a-49f0-85d3-3f72ed6a4542

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix n n O) {k : ℕ} {P : MvPolynomial n O}
    (hP : P.IsHomogeneous k) : (linSubst O n M P).IsHomogeneous k := by
  have h := hP.aeval (fun i => ∑ j, C (M i j) * X j) (n := 1)
    (fun i => IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _))
  simpa [linSubst] using h
end Formalism.UG.P
