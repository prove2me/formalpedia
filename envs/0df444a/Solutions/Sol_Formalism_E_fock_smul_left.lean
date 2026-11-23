-- Prove2me | solution 1 for Formalism.E.fock_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:25.474553+00:00
-- url     : https://prove2.me/submissions/50e6e6a6-bd17-45a3-81f4-dee50b37e298

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockSesq
import Theorems.Thm_Formalism_E_fock_eq_sum_of_subset

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
theorem _root_.solution (c : R) (f g : MvPolynomial τ R) : fock (c • f) g = c * fock f g := by
  classical
  rw [fock_eq_sum_of_subset (c • f) g f.support MvPolynomial.support_smul,
    fock_eq_sum_of_subset f g f.support (Finset.Subset.refl _), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)
end Formalism.E
