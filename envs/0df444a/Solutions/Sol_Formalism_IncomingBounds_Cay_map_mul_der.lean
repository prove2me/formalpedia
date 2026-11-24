-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.map_mul_der
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:05.606203+00:00
-- url     : https://prove2.me/submissions/e311a1d0-0014-4471-a64f-2ceacd1d24c1

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
open MvPolynomial Matrix
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A)
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {n : Type*} [Fintype n] (X Y : Matrix n n A) :
    (X * Y).map D = X.map D * Y + X * Y.map D := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring
end Formalism.IncomingBounds.Cay
