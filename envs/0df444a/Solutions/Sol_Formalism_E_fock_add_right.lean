-- Prove2me | solution 1 for Formalism.E.fock_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:25.603026+00:00
-- url     : https://prove2.me/submissions/a9c05348-49b2-4535-95a0-6ef2450fe99c

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockSesq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MvPolynomial
open Formalism Formalism.E
variable {R τ : Type*} [CommRing R] [StarRing R]
namespace Formalism.E
theorem _root_.solution (f g g' : MvPolynomial τ R) : fock f (g + g') = fock f g + fock f g' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add, star_add]; ring)
end Formalism.E
