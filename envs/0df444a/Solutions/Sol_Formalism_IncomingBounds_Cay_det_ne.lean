-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:04.069676+00:00
-- url     : https://prove2.me/submissions/ced924c6-cf3d-4e92-80aa-2ba148982ca9

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution (n : ℕ) : (Mg K n).det ≠ 0 := by
  let φ : Formalism.IncomingBounds.PVar n → K := Sum.elim (fun p => if p.1 = p.2 then 1 else 0) (fun _ => 0)
  have h3 : (MvPolynomial.eval φ).mapMatrix (Mg K n) = 1 := by
    ext i j
    simp [φ, Mg, Matrix.one_apply, RingHom.mapMatrix_apply]
  have key : MvPolynomial.eval φ (Mg K n).det = 1 := by
    rw [RingHom.map_det, h3, det_one]
  intro h
  rw [h, map_zero] at key
  exact zero_ne_one key
end Formalism.IncomingBounds.Cay
