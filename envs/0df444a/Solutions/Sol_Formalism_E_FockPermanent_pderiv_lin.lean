-- Prove2me | solution 1 for Formalism.E.FockPermanent.pderiv_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:33.339648+00:00
-- url     : https://prove2.me/submissions/aad12018-75e9-4f8e-9d41-36e1d45c7035

import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix MvPolynomial
noncomputable section
open Formalism Formalism.E
open Formalism.E.FockPermanent
variable {R τ : Type*} [CommRing R]
namespace Formalism.E.FockPermanent
theorem _root_.solution (z : MvPolynomial τ R) (hz : z.IsHomogeneous 1) (k : τ) :
    pderiv k z = C (z.coeff (Finsupp.single k 1)) := by
  classical
  ext m
  rw [coeff_pderiv, coeff_C]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg (Ne.symm hm), hz.coeff_eq_zero, zero_mul]
    rw [map_add, Finsupp.degree_single]
    intro h; apply hm
    rw [← Finsupp.degree_eq_zero_iff]; omega
end Formalism.E.FockPermanent
