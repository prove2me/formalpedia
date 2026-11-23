-- Prove2me | solution 1 for Formalism.E.fock_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:06.464807+00:00
-- url     : https://prove2.me/submissions/00fc4fa6-f98d-4572-840c-3fc6d2c42dfb

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
theorem _root_.solution (c : R) (f g : MvPolynomial τ R) :
    fock f (c • g) = star c * fock f g := by
  unfold fock
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by
    rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
    ring)
end Formalism.E
